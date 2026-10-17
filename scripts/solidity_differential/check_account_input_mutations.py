"""Compile and execute exact account-parser/installation semantic mutants."""
import argparse
import hashlib
from pathlib import Path

from .engine import HarnessError, command, write_json


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', required=True, type=Path)
    parser.add_argument('--reference', required=True, type=Path)
    args = parser.parse_args()
    output = args.output.resolve()
    output.mkdir(parents=True, exist_ok=False)
    account_path = Path('Compiler/SolidityImport/AccountsInput.lean')
    caller_path = Path('Compiler/SolidityImport/CallerInput.lean')
    runtime_path = Path('Contracts/SolidityImportSmoke/AccountInputChecks.lean')
    originals = {str(p): hashlib.sha256(p.read_bytes()).hexdigest()
                 for p in [account_path, caller_path, runtime_path]}
    # Correctness laws stay in the separately kernel-audited original modules.
    # An intentionally wrong definition must reach the unchanged runtime checks.
    accounts = account_path.read_text().split('\ntheorem install_storage', 1)[0]
    accounts += '\nend Compiler.CompilationModel.SolidityImport.AccountsInput\n'
    caller = caller_path.read_text().split('\ntheorem install_account', 1)[0]
    caller = caller.replace('import Compiler.SolidityImport.AccountsInput\n', '')
    caller += '\nend Compiler.CompilationModel.SolidityImport.CallerInput\n'
    runtime = runtime_path.read_text().replace('import Compiler.SolidityImport.CallerInput\n', '')
    source = accounts + '\n' + caller + '\n' + runtime
    cases = Path('scripts/solidity_differential/account_input_cases.json').resolve()
    reference = args.reference.resolve() / 'caller.json'
    command(['lake', 'env', 'lean', '--run', runtime_path, cases, reference],
            log=output / 'baseline.log')
    assert 'CALLER_INPUT_SUCCESS:' in (output / 'baseline.log').read_text()
    mutations = {
        'erase-external-nonce': ('return { address, account := { nonce,',
            'return { address, account := { nonce := nonce - nonce,', 'initial account boundary values changed'),
        'erase-external-code': ('then input.account else world.creationAccounts address',
            'then { input.account with code := ByteArray.empty } else world.creationAccounts address',
            'initial accounts changed code/nonce/balance'),
        'erase-external-balance': ('then input.account else world.creationAccounts address',
            'then { input.account with balance := 0 } else world.creationAccounts address',
            'initial accounts changed code/nonce/balance'),
        'wrong-code-size': ('Uint256.ofNat input.account.code.size else world.codeSize address',
            'Uint256.ofNat (input.account.code.size + 1) else world.codeSize address',
            'initial accounts changed code/nonce/balance'),
        'allow-reserved': ('unless addresses.all (fun address => !reserved.contains address) do',
            'unless addresses.all (fun address => !reserved.contains address || address == address) do',
            'invalid account input accepted:'),
        'allow-nonce-overflow': ('(← json.getObjVal? "nonce") (2^64)',
            '(← json.getObjVal? "nonce") (2^256)', 'invalid account input accepted:'),
        'erase-self-balance': ('selfBalance := caller.account.balance', 'selfBalance := 0',
            'actual caller metadata changed during Lean installation'),
        'accept-wrong-target': ('unless caller.address == target do',
            'unless caller.address == target || caller.address == caller.address do',
            'mismatched caller target accepted'),
        'accept-sender-collision': ('unless !senders.contains caller.address do',
            'unless !senders.contains caller.address || caller.address == caller.address do',
            'caller/sender collision accepted'),
    }
    rows = []
    for name, (before, after, diagnostic) in mutations.items():
        assert source.count(before) == 1, (name, source.count(before))
        text = source.replace(before, after)
        path = output / (name + '.lean')
        path.write_text(text)
        command(['lake', 'env', 'lean', path], log=output / (name + '-compile.log'))
        clean = (output / (name + '-compile.log')).read_text()
        assert not any(word in clean for word in ['error:', 'warning:', 'sorryAx'])
        failures = []
        for suffix in ['', '-replay']:
            log = output / (name + suffix + '.log')
            try:
                command(['lake', 'env', 'lean', '--run', path, cases, reference], log=log)
            except HarnessError as failure:
                assert 'tool_failure (1)' in str(failure)
                actual = log.read_text()
                assert 'uncaught exception: ' + diagnostic in actual, (name, actual)
                assert not any(word in actual for word in ['error:', 'warning:', 'sorryAx'])
                assert 'CALLER_INPUT_SUCCESS:' not in actual
                failures.append(actual.split('uncaught exception: ', 1)[1].strip())
            else:
                raise AssertionError('account input semantic mutant survived: ' + name)
        assert len(failures) == 2 and failures[0] == failures[1]
        rows.append({'name': name, 'sourceSha256': hashlib.sha256(text.encode()).hexdigest(),
                     'detected': failures[0], 'replay': failures[1]})
    assert originals == {p: hashlib.sha256(Path(p).read_bytes()).hexdigest() for p in originals}
    write_json(output / 'success.json', {'mutants': rows, 'sourceHashes': originals,
        'scriptSha256': hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        'sourcesUnchanged': True, 'scope': 'Nine clean-compiled input semantic mutants with unchanged runtime assertions'})
    print('PASS nine account input Lean semantic mutants, each detected and independently replayed')


if __name__ == '__main__':
    main()
