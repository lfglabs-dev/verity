"""A/B/C differential check for Yul dynamic memory-array length shrinks (Refs #2620).

Replays `YulArrayLengthShrinkSequence.sol` across source EVM (solc), Denote (imported
CompilationModel), and compiled model (Verity Yul -> solc -> EVM) on both the via-IR and
legacy pipelines across pinned solc 0.8.38 (cancun and osaka) and solc 0.8.34 (osaka):

* shrink-to-0 (uninitialized list, initialized empty list, end-of-list cursor, literal 0,
  `returnedShrunkArray(cap, 0, ...)`, `filterCompact(0, 0, 0, 0)`, `helperShrinkSub(3, ...)`);
* shrink-to-partial (paginated multi-entry list with `count < pageSize`, post-shrink memory
  allocation, `returnedShrunkArray(cap, keep, ...)`, `filterCompact` with mixed zeros,
  `helperShrinkSub(1..2, ...)`, `shrinkNarrowAndZero`);
* no-shrink (`pageSize == 0`, full page `count == pageSize`, `keep == cap`, `drop == 0`);
* returned array ABI encoding after shrink (lone `uint256[]` / `bytes32[]` / `uint16[]` and
  tuple `(address[], address)` / `(address[], address, uint256)` over non-zero trailing words);
* post-shrink `.length`, alias `.length`, helper iteration, `abi.encode`, in-bounds `xs[i]`,
  and out-of-bounds `xs[keep]` (`Panic(0x32)` with state rollback).
"""
import argparse
import hashlib
from pathlib import Path
import random
import sys
import tempfile

from .anvil import SequenceAdapter as EVM
from .denote import SequenceAdapter as Denote
from .engine import ROOT, SOLC, WORKSPACE, HarnessError, command, solc_compile, write_json
from .stateful import replay_three_routes, shrink_sequence

FIXTURE = Path('Contracts/SolidityImportSmoke/YulArrayLengthShrinkSequence.sol')
CONTRACT = 'YulArrayLengthShrinkFixture'
SENDER = '0xf39fd6e51aad88f6f4ce6ab8827279cfffb92266'
# Deterministic CREATE address of Anvil's default deployer `SENDER` at nonce 0.
DEPLOYED_CONTRACT = '0x5fbdb2315678afecb367f032d93f642f64180aa3'
SENTINEL = '0x' + '00' * 19 + '01'
ITEMS = (
    '0x' + '00' * 19 + 'a1',
    '0x' + '00' * 19 + 'b2',
    '0x' + '00' * 19 + 'c3',
    '0x' + '00' * 19 + 'd4',
)
MAX_UINT256 = (1 << 256) - 1
PANIC_ARRAY_BOUNDS = '0x4e487b71' + f'{0x32:064x}'

SIGNATURES = {
    'initList': 'initList()',
    'addItem': 'addItem(address)',
    'fail': 'fail()',
    'readState': 'readState()',
    'paginate': 'paginate(address,uint256)',
    'paginateThenAllocate': 'paginateThenAllocate(address,uint256,uint256)',
    'returnedShrunkArray': 'returnedShrunkArray(uint256,uint256,uint256)',
    'inspectPostShrink': 'inspectPostShrink(uint256,uint256,uint256)',
    'filterCompact': 'filterCompact(uint256,uint256,uint256,uint256)',
    'helperShrinkSub': 'helperShrinkSub(uint256,uint256)',
    'helperConstShadow': 'helperConstShadow(uint256,uint256)',
    'shrinkNarrowAndZero': 'shrinkNarrowAndZero(uint256,uint256,bool)',
}

PROFILES = (
    ('0834-osaka-viair', 'solc-0.8.34', '0.8.34+commit.80d5c536', 'osaka', True, 466),
    ('0834-osaka-legacy', 'solc-0.8.34', '0.8.34+commit.80d5c536', 'osaka', False, 466),
    ('0838-cancun-viair', 'solc-0.8.38', '0.8.38+commit.1835d247', 'cancun', True, 10),
    ('0838-cancun-legacy', 'solc-0.8.38', '0.8.38+commit.1835d247', 'cancun', False, 10),
    ('0838-osaka-viair', 'solc-0.8.38', '0.8.38+commit.1835d247', 'osaka', True, 466),
    ('0838-osaka-legacy', 'solc-0.8.38', '0.8.38+commit.1835d247', 'osaka', False, 466),
)


def solc_binary(name):
    for root in (ROOT, WORKSPACE):
        candidate = root / '.lake/solidity-import' / name
        if candidate.exists():
            return candidate
    if name == 'solc-0.8.34' and SOLC.exists():
        return SOLC
    raise HarnessError(f'missing pinned solc binary {name}; run python3 scripts/setup_solc_import.py --all')


def to_word(val):
    if isinstance(val, bool):
        return 1 if val else 0
    if isinstance(val, str):
        return int(val, 16)
    return int(val)


def parse_words(hex_data):
    body = hex_data[2:] if hex_data.startswith('0x') else hex_data
    if len(body) % 64 != 0:
        raise HarnessError(f'non-word-aligned ABI return data: {hex_data}')
    return [int(body[i:i + 64], 16) for i in range(0, len(body), 64)]


def word_to_addr(w):
    return f'0x{w & ((1 << 160) - 1):040x}'


def decode_dyn_array_at(words, byte_offset):
    if byte_offset % 32 != 0:
        raise HarnessError(f'unaligned dynamic array offset {byte_offset}')
    head = byte_offset // 32
    length = words[head]
    return words[head + 1:head + 1 + length]


def transactions_for(count, seed, contract, identifiers):
    rng = random.Random(seed)
    calls = []
    checks = []

    def add(name, values, check=None):
        sig = SIGNATURES[name]
        sel_hex = identifiers[sig]
        words = [to_word(v) for v in values]
        data_hex = '0x' + sel_hex + ''.join(f'{w:064x}' for w in words)
        idx = len(calls)
        calls.append({
            'id': str(idx),
            'function': name,
            'args': words,
            'sender': SENDER,
            'target': contract,
            'data': data_hex,
            'value': '0x0',
            'timestamp': 1000000100 + idx,
            'blockNumber': 2 + idx,
        })
        if check is not None:
            checks.append((str(idx), check))

    # 1. Shrink-to-0 on uninitialized list (`nextItem[SENTINEL] == address(0)`), then initialized empty list.
    add('paginate', [SENTINEL, 4], ('page', [], '0x' + '00' * 20))
    add('initList', [], ('ok',))
    add('paginate', [SENTINEL, 4], ('page', [], SENTINEL))
    add('paginateThenAllocate', [SENTINEL, 3, 0x55], ('page_alloc', [], SENTINEL, 0x55 + 7))

    # 2. Populate 3 items (inserted at head: ITEMS[2], ITEMS[1], ITEMS[0]).
    add('addItem', [ITEMS[0]], ('ok',))
    add('addItem', [ITEMS[1]], ('ok',))
    add('addItem', [ITEMS[2]], ('ok',))

    # 3. Paginated list: 0-cap no-shrink, partial-list full-page no-shrink, cursor continuation
    # shrink-to-partial, exact-fit no-shrink, and tail-cursor shrink-to-0.
    add('paginate', [SENTINEL, 0], ('page', [], ITEMS[2]))
    add('paginate', [SENTINEL, 2], ('page', [ITEMS[2], ITEMS[1]], ITEMS[1]))
    add('paginate', [ITEMS[1], 5], ('page', [ITEMS[0]], SENTINEL))
    add('paginate', [SENTINEL, 5], ('page', [ITEMS[2], ITEMS[1], ITEMS[0]], SENTINEL))
    add('paginate', [SENTINEL, 3], ('page', [ITEMS[2], ITEMS[1], ITEMS[0]], SENTINEL))
    add('paginate', [ITEMS[0], 4], ('page', [], SENTINEL))
    add('paginateThenAllocate', [SENTINEL, 5, 0x20],
        ('page_alloc', [ITEMS[2], ITEMS[1], ITEMS[0]], SENTINEL, (0x20 ^ 3) + 10))

    # 4. Lone returned array (ABI encoding after shrink over non-zero trailing words):
    # shrink-to-0, shrink-to-partial, no-shrink, and 0-cap no-shrink.
    add('returnedShrunkArray', [5, 0, 7], ('uint_arr', []))
    add('returnedShrunkArray', [5, 2, 7], ('uint_arr', [107, 108]))
    add('returnedShrunkArray', [4, 4, 9], ('uint_arr', [109, 110, 111, 112]))
    add('returnedShrunkArray', [0, 0, 3], ('uint_arr', []))

    # 5. Post-shrink `.length`, alias `.length`, helper read, `abi.encode`, in-bounds read,
    # and out-of-bounds `xs[keep]` (`Panic(0x32)` over retained physical memory word).
    add('inspectPostShrink', [5, 0, MAX_UINT256], ('inspect_ok', 0, 0))
    add('inspectPostShrink', [5, 3, 2], ('inspect_ok', 3, 0x1002))
    add('inspectPostShrink', [4, 4, 3], ('inspect_ok', 4, 0x1003))
    add('readState', [], ('ok',))
    add('inspectPostShrink', [5, 2, 2], ('panic32',))
    add('inspectPostShrink', [5, 0, 0], ('panic32',))
    add('readState', [], ('ok',))
    add('fail', [], ('revert',))

    # 6. `for`-loop filtered compaction, straight-line array helper shrink, and narrow `uint16[]`.
    add('filterCompact', [0, 0, 0, 0], ('b32_len', 0))
    add('filterCompact', [11, 0, 22, 0], ('b32_len', 2))
    add('filterCompact', [1, 2, 3, 4], ('b32_len', 4))
    add('helperShrinkSub', [3, 50], ('uint_arr', []))
    add('helperShrinkSub', [1, 50], ('uint_arr', [60, 70]))
    add('helperShrinkSub', [0, 50], ('uint_arr', [60, 70, 80]))
    add('helperConstShadow', [4, 10], ('uint_arr', [16, 17, 18]))
    add('shrinkNarrowAndZero', [4, 2, False], ('uint_arr', [0x0200, 0x0201]))
    add('shrinkNarrowAndZero', [4, 2, True], ('uint_arr', []))
    add('shrinkNarrowAndZero', [3, 3, False], ('uint_arr', [0x0200, 0x0201, 0x0202]))

    while len(calls) < count:
        choice = rng.randrange(9)
        if choice == 0:
            cursor = rng.choice([SENTINEL, *ITEMS])
            add('paginate', [cursor, rng.randrange(0, 9)])
        elif choice == 1:
            cursor = rng.choice([SENTINEL, *ITEMS])
            add('paginateThenAllocate', [cursor, rng.randrange(0, 9), rng.randrange(0, 256)])
        elif choice == 2:
            cap = rng.randrange(0, 8)
            keep = rng.randrange(0, cap + 2)
            add('returnedShrunkArray', [cap, keep, rng.randrange(0, 1000)])
        elif choice == 3:
            cap = rng.randrange(0, 7)
            keep = rng.randrange(0, cap + 1)
            probe = rng.choice([MAX_UINT256, 0, keep, max(0, keep - 1), cap])
            add('inspectPostShrink', [cap, keep, probe])
        elif choice == 4:
            vals = [rng.choice([0, rng.randrange(1, 500)]) for _ in range(4)]
            add('filterCompact', vals)
        elif choice == 5:
            add('helperShrinkSub', [rng.randrange(0, 5), rng.randrange(0, 200)])
        elif choice == 6:
            cap = rng.randrange(0, 7)
            mid = rng.randrange(0, cap + 2)
            add('shrinkNarrowAndZero', [cap, mid, bool(rng.randrange(2))])
        elif choice == 7:
            add('addItem', [rng.choice(ITEMS)])
        else:
            add('readState', [])
    return calls, checks


def verify_non_vacuous(rows_by_id, checks):
    for ident, spec in checks:
        row = rows_by_id[ident]
        kind = spec[0]
        if kind == 'ok':
            if row['status'] != 'ok':
                raise HarnessError(f'tx {ident}: expected ok, got {row}')
        elif kind == 'revert':
            if row['status'] != 'revert':
                raise HarnessError(f'tx {ident}: expected revert, got {row}')
        elif kind == 'panic32':
            if row['status'] != 'revert' or row['data'].lower() != PANIC_ARRAY_BOUNDS:
                raise HarnessError(f'tx {ident}: expected Panic(0x32), got {row}')
        elif kind == 'page':
            _, want_page, want_next = spec
            if row['status'] != 'ok':
                raise HarnessError(f'tx {ident}: expected ok page, got {row}')
            words = parse_words(row['data'])
            got_page = [word_to_addr(w) for w in decode_dyn_array_at(words, words[0])]
            got_next = word_to_addr(words[1])
            if got_page != [a.lower() for a in want_page] or got_next != want_next.lower():
                raise HarnessError(
                    f'tx {ident}: expected {(want_page, want_next)}, got {(got_page, got_next)}')
        elif kind == 'page_alloc':
            _, want_page, want_next, want_sum = spec
            if row['status'] != 'ok':
                raise HarnessError(f'tx {ident}: expected ok page_alloc, got {row}')
            words = parse_words(row['data'])
            got_page = [word_to_addr(w) for w in decode_dyn_array_at(words, words[0])]
            got_next = word_to_addr(words[1])
            got_sum = words[2]
            if (got_page != [a.lower() for a in want_page]
                    or got_next != want_next.lower() or got_sum != want_sum):
                raise HarnessError(
                    f'tx {ident}: expected {(want_page, want_next, want_sum)}, '
                    f'got {(got_page, got_next, got_sum)}')
        elif kind == 'uint_arr':
            _, want_arr = spec
            if row['status'] != 'ok':
                raise HarnessError(f'tx {ident}: expected ok array, got {row}')
            words = parse_words(row['data'])
            got_arr = decode_dyn_array_at(words, words[0])
            if got_arr != want_arr:
                raise HarnessError(f'tx {ident}: expected {want_arr}, got {got_arr}')
        elif kind == 'inspect_ok':
            _, want_len, want_probed = spec
            if row['status'] != 'ok':
                raise HarnessError(f'tx {ident}: expected ok inspect, got {row}')
            words = parse_words(row['data'])
            got_len, got_probed, got_alias_len, _ = words
            if got_len != want_len or got_alias_len != want_len or got_probed != want_probed:
                raise HarnessError(
                    f'tx {ident}: expected len={want_len}, probed={want_probed}, '
                    f'got {(got_len, got_probed, got_alias_len)}')
        elif kind == 'b32_len':
            _, want_len = spec
            if row['status'] != 'ok':
                raise HarnessError(f'tx {ident}: expected ok bytes32[], got {row}')
            words = parse_words(row['data'])
            got_arr = decode_dyn_array_at(words, words[0])
            if len(got_arr) != want_len:
                raise HarnessError(f'tx {ident}: expected len {want_len}, got {len(got_arr)}')


def render_custom_driver(directory, solc_commit, evm_version, via_ir, runs):
    via_lit = 'true' if via_ir else 'false'
    evm_ctor = '.cancun' if evm_version == 'cancun' else '.osaka'
    fn_lines = '\n'.join(f'  function {sig}' for sig in SIGNATURES.values())
    driver = directory / 'Driver.lean'
    driver.write_text(f'''import Compiler.SolidityImport.Import
import Compiler.SolidityImport.SequenceRunner
import Compiler.SolidityImport.Differential
import Compiler.CompilationModel
import Compiler.Codegen
import Compiler.Yul.PrettyPrint

namespace CustomShrinkSequenceModel
open Compiler.CompilationModel
solidity_import imported from "{directory}" entry "Sequence.sol"
  using {{ solc := "{solc_commit}", evmVersion := "{evm_version}", viaIR := {via_lit}, optimizerRuns := some {runs}, bytecodeHash := "none" }}
  contract {CONTRACT}
{fn_lines}
def model : CompilationModel := imported.model
def oracle : Denote.DenoteOracle := SolidityImport.Differential.oracle
end CustomShrinkSequenceModel

def main (args : List String) : IO UInt32 := do
  match args with
  | ["compile", selectorsFile, output] =>
      let parsed ← IO.ofExcept (Lean.Json.parse (← IO.FS.readFile selectorsFile))
      let selectors ← IO.ofExcept do
        (← parsed.getArr?).toList.mapM fun j => j.getNat?
      let compiled ← IO.ofExcept (Compiler.CompilationModel.compile
        CustomShrinkSequenceModel.model selectors {evm_ctor})
      IO.FS.writeFile output (Compiler.Yul.render (Compiler.emitYulSpilled compiled))
      return 0
  | _ =>
      Compiler.CompilationModel.SolidityImport.SequenceRunner.run
        CustomShrinkSequenceModel.model CustomShrinkSequenceModel.oracle args
''')
    return driver


def run_profile(directory, source, profile, transactions, seed, shrink_attempts,
                source_override=None):
    label, solc_name, solc_commit, evm_version, via_ir, runs = profile
    directory = Path(directory).resolve()
    directory.mkdir(parents=True, exist_ok=True)
    solc_bin = solc_binary(solc_name)
    (directory / 'Sequence.sol').write_text(source)
    driver = render_custom_driver(directory, solc_commit, evm_version, via_ir, runs)

    settings = {
        'evmVersion': evm_version,
        'viaIR': via_ir,
        'optimizer': {'enabled': True, 'runs': runs},
        'metadata': {'bytecodeHash': 'none'},
        'outputSelection': {'*': {'*': ['evm.bytecode.object', 'evm.methodIdentifiers']}},
    }
    evm_source_text = source if source_override is None else source_override
    compiled = solc_compile(
        {'language': 'Solidity', 'sources': {'Sequence.sol': {'content': evm_source_text}},
         'settings': settings},
        directory, directory / 'solc', solc=solc_bin,
    )['contracts']['Sequence.sol'][CONTRACT]
    identifiers = compiled['evm']['methodIdentifiers']
    write_json(directory / 'selectors.json',
               [int(identifiers[sig], 16) for sig in SIGNATURES.values()])
    command(['lake', 'env', 'lean', '--run', driver, 'compile', directory / 'selectors.json',
             directory / 'model.yul'], cwd=WORKSPACE, timeout=900, log=directory / 'compile.log')
    generated = solc_compile({
        'language': 'Yul',
        'sources': {'Model.yul': {'content': (directory / 'model.yul').read_text()}},
        'settings': {'evmVersion': evm_version, 'optimizer': {'enabled': True, 'runs': runs},
                     'outputSelection': {'*': {'*': ['evm.bytecode.object']}}},
    }, directory, directory / 'compiled-solc', solc=solc_bin)['contracts']['Model.yul']
    if len(generated) != 1:
        raise HarnessError('expected exactly one compiled model object')
    source_code = '0x' + compiled['evm']['bytecode']['object']
    compiled_code = '0x' + next(iter(generated.values()))['evm']['bytecode']['object']
    calls, checks = transactions_for(transactions, seed, DEPLOYED_CONTRACT, identifiers)
    write_json(directory / 'transactions.json', calls)
    adapters = {
        'source': EVM(directory / 'A', [source_code], []),
        'model': Denote(directory / 'B', driver, DEPLOYED_CONTRACT, []),
        'compiled': EVM(directory / 'C', [compiled_code], []),
    }
    result = replay_three_routes(calls, adapters)
    report = {
        'profile': label,
        'transactions': calls,
        'observations': result['observations'],
        'divergences': result['divergences'],
        'seed': seed,
        'sourceSha256': hashlib.sha256(source.encode()).hexdigest(),
        'driverSha256': hashlib.sha256(driver.read_bytes()).hexdigest(),
    }
    if result['divergences']:
        reduced = shrink_sequence(
            calls,
            lambda txs: replay_three_routes(txs, adapters)['divergences'],
            max_attempts=shrink_attempts,
        )
        write_json(directory / 'reduced.json', reduced)
        write_json(directory / 'campaign.json', report)
        return 1, report
    verify_non_vacuous({r['id']: r for r in result['observations']['source']}, checks)
    write_json(directory / 'campaign.json', report)
    return 0, report


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--transactions', type=int, default=64)
    parser.add_argument('--seed', type=int, default=2620)
    parser.add_argument('--shrink-attempts', type=int, default=120)
    parser.add_argument('--profile', choices=[p[0] for p in PROFILES], action='append',
                        help='specific profile(s) to run (default: all 6 pinned profiles)')
    parser.add_argument('--source-fixture', type=Path, default=FIXTURE)
    parser.add_argument('--negative-control', action='store_true',
                        help='omit the length mstore on the source route and require A/B/C divergence')
    parser.add_argument('--output', type=Path)
    args = parser.parse_args()
    lake_tmp = WORKSPACE / '.lake'
    lake_tmp.mkdir(parents=True, exist_ok=True)
    output = (args.output.resolve() if args.output else
              Path(tempfile.mkdtemp(prefix='yul-array-length-shrink-', dir=lake_tmp)).resolve())
    output.mkdir(parents=True, exist_ok=True)
    source = args.source_fixture.read_text()

    if args.negative_control:
        mutated = source.replace('mstore(xs, keep)', 'pop(keep)')
        if mutated == source:
            raise HarnessError('negative control anchor missing')
        code, report = run_profile(output / 'negative-control', source, PROFILES[0],
                                   max(36, args.transactions), args.seed, 30,
                                   source_override=mutated)
        if not code:
            raise SystemExit(f'negative control (dropped mstore on source route) went undetected: {output}')
        if (output / 'negative-control/reduced.json').exists():
            (output / 'reduced.json').write_text((output / 'negative-control/reduced.json').read_text())
        write_json(output / 'campaign.json', report)
        print(f'yul array length shrink negative control diverges as expected: {output}')
        return 0

    selected = [p for p in PROFILES if not args.profile or p[0] in args.profile]
    summaries = []
    last_report = None
    for profile in selected:
        sub = output / profile[0]
        code, report = run_profile(sub, source, profile, args.transactions, args.seed,
                                   args.shrink_attempts)
        last_report = report
        if code:
            if (sub / 'reduced.json').exists():
                (output / 'reduced.json').write_text((sub / 'reduced.json').read_text())
            write_json(output / 'campaign.json', report)
            raise SystemExit(f'yul array length shrink divergence on {profile[0]}: {sub}')
        summaries.append({'profile': profile[0], 'transactions': len(report['transactions'])})
        print(f'pass yul-array-length-shrink {profile[0]} ({len(report["transactions"])} txs)',
              flush=True)
    if last_report is not None:
        write_json(output / 'campaign.json', last_report)
    write_json(output / 'summary.json', {
        'passed': True,
        'profiles': summaries,
        'seed': args.seed,
    })
    print(f'yul array length shrink A/B/C agree across {len(summaries)} profiles: {output}')
    return 0


if __name__ == '__main__':
    sys.exit(main())
