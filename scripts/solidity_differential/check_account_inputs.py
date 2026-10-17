"""Exact initial-account installation and receipt-pinned caller metadata controls."""
import argparse
import copy
import hashlib
import json
from pathlib import Path
import types

from .accounts import canonical_accounts, install_accounts
from .caller import canonical_caller, capture_caller, caller_json
from .anvil import Anvil
from .engine import HarnessError, command, write_json
from . import accounts as accounts_module, caller as caller_module


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', required=True, type=Path)
    args = parser.parse_args()
    output = args.output.resolve()
    output.mkdir(parents=True, exist_ok=False)
    address = lambda n: '0x' + format(n, '040x')
    entries = [
        {'address': address(65536), 'code': '0x', 'nonce': 0, 'balance': 0},
        {'address': address(65537), 'code': '0x0001', 'nonce': 7, 'balance': 13},
        {'address': address(65538), 'code': '0x60006000f3', 'nonce': 2**64-1, 'balance': 2**256-1},
    ]
    assert canonical_accounts(entries) == entries and canonical_accounts([]) == []
    invalid = []
    for key, values in [('address', ['0x1', address(1).upper(), None]),
                        ('code', ['0x0', '0xGG', None]),
                        ('nonce', [-1, 2**64, True, '0']),
                        ('balance', [-1, 2**256, False, '0'])]:
        for value in values:
            item = copy.deepcopy(entries[:1])
            item[0][key] = value
            invalid.append(item)
    invalid += [entries + entries[:1], [{'address': address(1)}],
                [dict(entries[0], extra=0)], [None]]
    for data in invalid:
        try:
            canonical_accounts(data)
        except HarnessError:
            pass
        else:
            raise AssertionError('accepted malformed initial accounts')
    try:
        canonical_accounts(entries, [entries[1]['address']])
    except HarnessError:
        pass
    else:
        raise AssertionError('allowed reserved account overwrite')
    mutations = []
    with Anvil(output / 'node') as node:
        reserved = node.rpc('eth_accounts')
        assert install_accounts(node, entries, reserved) == entries
        # Validate the entire list before any RPC mutation.
        before = node.rpc('eth_getCode', entries[0]['address'], 'latest')
        try:
            install_accounts(node, [dict(entries[0], code='0x6000'), entries[0]], reserved)
        except HarnessError:
            pass
        else:
            raise AssertionError('accepted duplicate account')
        assert node.rpc('eth_getCode', entries[0]['address'], 'latest') == before
        source = Path(accounts_module.__file__).read_text()
        for field, call in [('code', "node.rpc('anvil_setCode', address, account['code'])"),
                            ('nonce', "node.rpc('anvil_setNonce', address, hex(account['nonce']))"),
                            ('balance', "node.rpc('anvil_setBalance', address, hex(account['balance']))")]:
            assert source.count(call) == 1
            text = source.replace(call, 'pass')
            path = output / ('omit-' + field + '.py')
            path.write_text(text)
            module = types.ModuleType('mutant_account_input')
            exec(compile(text, str(path), 'exec'), module.__dict__)
            for replay in range(2):
                snapshot = node.rpc('evm_snapshot')
                target = {'address': address(70000), 'code': '0x0001', 'nonce': 7, 'balance': 13}
                try:
                    module.install_accounts(node, [target], reserved)
                except HarnessError as failure:
                    assert str(failure) == 'initial account installation changed the supplied world'
                else:
                    raise AssertionError('account installation mutant survived: ' + field)
                assert node.rpc('evm_revert', snapshot) is True
            mutations.append({'name': 'omit-' + field, 'semanticDetections': 2,
                              'sourceSha256': hashlib.sha256(text.encode()).hexdigest()})
        creation = '0x6100016000526002601ef3'
        deployment = node.transact({'from': reserved[0], 'data': creation,
                                   'gas': hex(1000000), 'value': '0xd'})
        receipt = deployment['receipt']
        initial = capture_caller(node, receipt)
        target = initial['account']['address']
        assert initial['account'] == {'address': target, 'code': '0x0001', 'nonce': 1, 'balance': 13}
        node.transact({'from': reserved[0], 'to': reserved[0], 'value': '0x0', 'gas': hex(21000)})
        node.rpc('anvil_setCode', target, '0x6000')
        node.rpc('anvil_setNonce', target, '0x7')
        node.rpc('anvil_setBalance', target, '0x17')
        assert capture_caller(node, receipt) == initial
        assert node.rpc('eth_getCode', target, 'latest') == '0x6000'
        assert int(node.rpc('eth_getTransactionCount', target, 'latest'), 16) == 7
        assert int(node.rpc('eth_getBalance', target, 'latest'), 16) == 23
        controls = [
            lambda: canonical_caller(initial['account'], address(1)),
            lambda: canonical_caller(initial['account'], target, [target]),
            lambda: capture_caller(node, {**receipt, 'status': '0x0'}),
            lambda: capture_caller(node, {**receipt, 'blockHash': '0x' + '00' * 32}),
            lambda: canonical_caller({**initial['account'], 'nonce': True}, target),
            lambda: canonical_caller({**initial['account'], 'nonce': 2**64}, target),
        ]
        for reject in controls:
            try:
                reject()
            except HarnessError:
                pass
            else:
                raise AssertionError('invalid caller metadata accepted')
        source = Path(caller_module.__file__).read_text()
        corruptions = {
            'latest-code': ("node.rpc('eth_getCode', address, block)", "node.rpc('eth_getCode', address, 'latest')"),
            'erase-nonce': ("int(node.rpc('eth_getTransactionCount', address, block), 16)", '0'),
            'drop-leading-code-byte': ("node.rpc('eth_getCode', address, block)", "'0x' + node.rpc('eth_getCode', address, block)[4:]"),
        }
        for name, (old, new) in corruptions.items():
            assert source.count(old) == 1
            text = source.replace(old, new)
            path = output / (name + '.py')
            path.write_text(text)
            module = types.ModuleType('mutant_caller_input')
            exec(compile(text, str(path), 'exec'), module.__dict__)
            for replay in range(2):
                # Actual successful RPC capture with a semantically wrong account.
                wrong = module.capture_caller(node, receipt)
                assert wrong['account'] != initial['account'], name
            mutations.append({'name': name, 'semanticDetections': 2,
                              'sourceSha256': hashlib.sha256(text.encode()).hexdigest()})
    caller_record = {'json': caller_json(initial['account']), 'initial': initial,
                     'receipt': receipt, 'creationCode': creation}
    write_json(output / 'caller.json', caller_record)
    # Checked-in JSON covers exact canonical parsing and all staged near misses.
    cases = Path('scripts/solidity_differential/account_input_cases.json').resolve()
    command(['lake', 'env', 'lean', '--run', 'Contracts/SolidityImportSmoke/AccountInputChecks.lean',
             cases, output / 'caller.json'], log=output / 'lean.log', timeout=180)
    log = (output / 'lean.log').read_text()
    assert 'ACCOUNT_INPUT_SUCCESS:27 exact input/world cases' in log
    assert 'CALLER_INPUT_SUCCESS: exact actual deployment metadata; two target/sender refusals' in log
    assert not any(token in log for token in ['error:', 'warning:', 'sorryAx'])
    inputs = [Path(__file__), Path(accounts_module.__file__), Path(caller_module.__file__), cases,
              Path('Compiler/SolidityImport/AccountsInput.lean'),
              Path('Compiler/SolidityImport/CallerInput.lean'),
              Path('Contracts/SolidityImportSmoke/AccountInputChecks.lean')]
    write_json(output / 'success.json', {'accounts': entries, 'caller': caller_record,
        'externalRefusals': len(invalid) + 2, 'callerRefusals': len(controls),
        'mutations': mutations, 'leanCases': 27,
        'sourceHashes': {str(p.resolve()): hashlib.sha256(p.read_bytes()).hexdigest() for p in inputs},
        'scope': 'Exact input/world parsing, real deployment capture and semantic mutations; no CREATE2 admission'})
    print('PASS account input controls:27 Lean cases, exact real caller capture, six Python semantic mutants with replays')


if __name__ == '__main__':
    main()
