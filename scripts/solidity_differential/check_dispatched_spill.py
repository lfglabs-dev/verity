"""End-to-end differential and adversarial-reproducer check for per-dispatch-case Yul spilling.

Compiles both baseline (unspilled) and `Compiler.emitYulSpilled` Yul outputs produced by
`Contracts/SolidityImportSmoke/DispatchedSpillChecks.lean` with `solc --strict-assembly`
(`--evm-version cancun`) and compares their execution on `anvil`:

1. `DispatchedSpillDifferential`:
   - `0x11111111` (`hashAfterSpillAndAlloc`): >12 live locals, allocates heap via the checked
     allocation idiom and hashes the allocated words; verified spilled in Yul (`mstore(4096, ...)`
     and `mstore(64, highWater)`) and identical to baseline on `anvil` (return words + storage).
   - `0x22222222` (`echoDynamicTail`): >12 live locals, returns a dynamic `uint256[]` including
     payloads > 4 KiB (200 words = 6,464 bytes); verified unspilled in Yul and identical to
     baseline on `anvil`.
2. Adversarial EVM reproducers 1-7 (`repro1`..`repro7b`):
   - Reproducer 1: in-case `mstore(64, 128)` before `return(0, 96)` -> `[105, 99, 128]`.
   - Reproducer 2: `mstore(add(p, 2^256 - 32), 999999)` wraparound -> `[105]`.
   - Reproducer 3: conditional `mload(64)` before `return(0, 96)` -> `[105, 0, 128]`.
   - Reproducer 4: fallback `mload(64)` + heap word at 4096 + inner `switch` -> `[777]`.
   - Reproducer 5: static `mload(128)` aliasing `mload(64)` heap -> `[216]`.
   - Reproducer 6: near-`2^64` checked-allocation reserve (`2^64 - 129`) -> `[105]`.
   - Reproducer 7a/7b: `break` / `continue` before `revert` after `mstore(64, 0)` -> `[105]`.
"""
from __future__ import annotations

import argparse
from pathlib import Path
import re
import tempfile

from .anvil import Anvil
from .engine import SOLC, HarnessError, command, write_json


DRIVER = 'Contracts/SolidityImportSmoke/DispatchedSpillChecks.lean'


def assemble_strict_yul(yul_path: Path, log_path: Path) -> str:
    """Assemble standalone Yul with `solc --strict-assembly --evm-version cancun --bin`."""
    out = command(
        [str(SOLC), '--strict-assembly', '--evm-version', 'cancun', '--bin', str(yul_path)],
        timeout=120,
        log=log_path,
    )
    hex_lines = [
        line.strip()
        for line in out.splitlines()
        if re.fullmatch(r'[0-9a-fA-F]+', line.strip())
    ]
    if not hex_lines:
        raise HarnessError(f'solc --strict-assembly produced no binary for {yul_path}')
    return '0x' + hex_lines[-1].lower()


def decode_words(hex_data: str) -> list[int]:
    raw = hex_data[2:] if hex_data.startswith('0x') else hex_data
    if len(raw) % 64 != 0:
        raise HarnessError(f'non-word-aligned return data: {hex_data}')
    return [int(raw[i:i + 64], 16) for i in range(0, len(raw), 64)]


def encode_u256(v: int) -> str:
    return f'{v & ((1 << 256) - 1):064x}'


def encode_echo_calldata(a: int, b: int, c: int, d: int, values: list[int]) -> str:
    head = (
        encode_u256(a)
        + encode_u256(b)
        + encode_u256(c)
        + encode_u256(d)
        + encode_u256(5 * 32)
    )
    tail = encode_u256(len(values)) + ''.join(encode_u256(x) for x in values)
    return '0x22222222' + head + tail


def run_check(output: Path) -> dict:
    output = output.resolve()
    output.mkdir(parents=True, exist_ok=True)
    yul_dir = output / 'yul'
    command(
        ['lake', 'env', 'lean', '--run', DRIVER, str(yul_dir)],
        timeout=600,
        log=output / 'emit.log',
    )

    diff_spilled_text = (yul_dir / 'differential.spilled.yul').read_text(encoding='utf-8')
    if 'mstore(4096,' not in diff_spilled_text or 'mload(4096)' not in diff_spilled_text:
        raise HarnessError('expected spill slot 4096 in differential.spilled.yul')

    stems = (
        'differential',
        'repro1',
        'repro2',
        'repro3',
        'repro4',
        'repro5',
        'repro6',
        'repro7a',
        'repro7b',
    )
    binaries: dict[str, tuple[str, str]] = {}
    for stem in stems:
        base_bin = assemble_strict_yul(
            yul_dir / f'{stem}.baseline.yul', output / f'{stem}.baseline.solc.log'
        )
        spilled_bin = assemble_strict_yul(
            yul_dir / f'{stem}.spilled.yul', output / f'{stem}.spilled.solc.log'
        )
        binaries[stem] = (base_bin, spilled_bin)

    slot0 = '0x' + '00' * 32
    slot1 = '0x' + '00' * 31 + '01'
    comparisons = []

    with Anvil(output / 'anvil', hardfork='cancun') as node:
        sender = node.rpc('eth_accounts')[0]

        def deploy_pair(stem: str) -> tuple[str, str]:
            b_code, s_code = binaries[stem]
            d_b = node.transact({'from': sender, 'data': b_code, 'gas': hex(5_000_000)})
            d_s = node.transact({'from': sender, 'data': s_code, 'gas': hex(5_000_000)})
            if d_b['receipt']['status'] != '0x1' or d_s['receipt']['status'] != '0x1':
                raise HarnessError(f'deployment failed for {stem}')
            return d_b['receipt']['contractAddress'], d_s['receipt']['contractAddress']

        def call_both(
            label: str, addr_b: str, addr_s: str, calldata: str, value: int = 0
        ) -> list[int]:
            rec_b = node.transact({
                'from': sender, 'to': addr_b, 'data': calldata,
                'value': hex(value), 'gas': hex(8_000_000),
            })
            rec_s = node.transact({
                'from': sender, 'to': addr_s, 'data': calldata,
                'value': hex(value), 'gas': hex(8_000_000),
            })
            obs_b = node.observe(rec_b, f'{label}-base', [(addr_b, slot0), (addr_b, slot1)])
            obs_s = node.observe(rec_s, f'{label}-spilled', [(addr_s, slot0), (addr_s, slot1)])
            if obs_b['status'] != obs_s['status'] or obs_b['data'] != obs_s['data']:
                raise HarnessError(
                    f'{label} return mismatch: baseline=({obs_b["status"]}, {obs_b["data"]}) '
                    f'vs spilled=({obs_s["status"]}, {obs_s["data"]})'
                )
            st_b = [row[2] for row in obs_b['storage']]
            st_s = [row[2] for row in obs_s['storage']]
            if st_b != st_s:
                raise HarnessError(f'{label} storage mismatch: {st_b} vs {st_s}')
            if obs_b['events'] != obs_s['events']:
                raise HarnessError(f'{label} event mismatch')
            comparisons.append({'label': label, 'status': obs_b['status'], 'bytes': len(obs_b['data']) // 2 - 1})
            return decode_words(obs_b['data'])

        # 1. End-to-end differential contract: heap allocation + >4 KiB dynamic array return.
        diff_b, diff_s = deploy_pair('differential')
        for idx, (a, b, c) in enumerate(((3, 5, 7), (0, 1, 2), ((1 << 128) + 9, 42, 99))):
            calldata = '0x11111111' + encode_u256(a) + encode_u256(b) + encode_u256(c)
            words = call_both(f'alloc-{idx}', diff_b, diff_s, calldata)
            if len(words) != 1:
                raise HarnessError(f'expected 1 word from alloc-{idx}, got {len(words)}')

        for length in (0, 3, 129, 200):
            arr = [(i * 17 + 3) for i in range(length)]
            calldata = encode_echo_calldata(2, 3, 5, 7, arr)
            words = call_both(f'dyn-{length}', diff_b, diff_s, calldata)
            expected = [32, length, *arr]
            if words != expected:
                raise HarnessError(f'dyn-{length} decoded mismatch: {words[:6]} vs {expected[:6]}')
            if length == 200 and len(words) * 32 <= 4096:
                raise HarnessError('expected > 4 KiB return payload for length=200')

        # 2. Adversarial reproducers 1-7.
        r1_b, r1_s = deploy_pair('repro1')
        if call_both('repro1', r1_b, r1_s, '0x11111111') != [105, 99, 128]:
            raise HarnessError('unexpected repro1 output')

        r2_b, r2_s = deploy_pair('repro2')
        if call_both('repro2', r2_b, r2_s, '0x22222222') != [105]:
            raise HarnessError('unexpected repro2 output')

        r3_b, r3_s = deploy_pair('repro3')
        if call_both('repro3-zero', r3_b, r3_s, '0x33333333' + encode_u256(0)) != [105, 0, 128]:
            raise HarnessError('unexpected repro3-zero output')
        if call_both('repro3-one', r3_b, r3_s, '0x33333333' + encode_u256(1)) != [105, 0, 128]:
            raise HarnessError('unexpected repro3-one output')

        r4_b, r4_s = deploy_pair('repro4')
        if call_both('repro4-fallback-miss', r4_b, r4_s, '0xdeadbeef' + encode_u256(3968)) != [777]:
            raise HarnessError('unexpected repro4 unknown-selector fallback output')

        r5_b, r5_s = deploy_pair('repro5')
        if call_both('repro5-static128', r5_b, r5_s, '0x55555555') != [216]:
            raise HarnessError('unexpected repro5 static-128 alias output')

        r6_b, r6_s = deploy_pair('repro6')
        if call_both('repro6-near-u64', r6_b, r6_s, '0x66666666' + encode_u256((1 << 64) - 129)) != [105]:
            raise HarnessError('unexpected repro6 near-u64 reserve output')

        r7a_b, r7a_s = deploy_pair('repro7a')
        if call_both('repro7a-break', r7a_b, r7a_s, '0x77777777' + encode_u256(1)) != [105]:
            raise HarnessError('unexpected repro7a break output')

        r7b_b, r7b_s = deploy_pair('repro7b')
        if call_both('repro7b-continue', r7b_b, r7b_s, '0x77777778' + encode_u256(1)) != [105]:
            raise HarnessError('unexpected repro7b continue output')

    summary = {'comparisons': comparisons}
    write_json(output / 'summary.json', summary)
    return summary


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument('--output', type=Path, default=None)
    args = parser.parse_args()
    out = args.output or Path(tempfile.mkdtemp(prefix='dispatched-spill-', dir='.lake'))
    run_check(out)
    print('Dispatched spill differential check and reproducers 1-7 passed on Anvil')


if __name__ == '__main__':
    main()
