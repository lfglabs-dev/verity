"""Real EVM deployment observations and adversarial comparator controls.

This is a source-only instrument campaign, not an A/B/C equivalence claim.
Denote does not yet execute deployment. Synthetic copies below exercise only
the comparator's ability to reject incomplete data and detect mutations.
"""
import argparse
import copy
import hashlib
from pathlib import Path

from .anvil import Anvil
from .deployment import (compare_deployment_sequences, observe_accounts, discover_create2_accounts,
                         DeploymentSequenceAdapter, replay_deployment_routes)
from .engine import HarnessError, SOLC, solc_compile, write_json
from .stateful import ROUTES

PREFIX = bytes.fromhex('600b380380600b5f395ff3')


def calldata(selector, salt, payload, fail):
    # (bytes32,bytes,bool): a three-word head and a byte-length-prefixed tail.
    words = [salt, 96, int(fail), len(payload)]
    return '0x' + selector + ''.join(format(word, '064x') for word in words) + (
        payload + bytes((-len(payload)) % 32)).hex()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    out = args.output.resolve()
    out.mkdir(parents=True, exist_ok=False)
    fixture = Path(__file__).parent / 'fixtures/Deployment.sol'
    request = {'language': 'Solidity', 'sources': {'Deployment.sol': {'content': fixture.read_text()}},
               'settings': {'evmVersion': 'osaka', 'viaIR': True,
                            'optimizer': {'enabled': True, 'runs': 466},
                            'metadata': {'bytecodeHash': 'none'},
                            'outputSelection': {'*': {'*': ['evm.bytecode.object', 'evm.methodIdentifiers']}}}}
    evm = solc_compile(request, fixture.parent, out / 'source')['contracts']['Deployment.sol']['DeploymentFixture']['evm']
    selector = evm['methodIdentifiers']['deploy(bytes32,bytes,bool)']
    rows, plans, cases, controls, transactions = [], [], [], [], []
    with Anvil(out / 'node') as node:
        sender = node.rpc('eth_accounts')[0]
        deployed = node.transact({'from': sender, 'data': '0x' + evm['bytecode']['object'], 'gas': hex(10000000)})
        assert deployed['receipt']['status'] == '0x1'
        creator = deployed['receipt']['contractAddress']
        nonce = int(node.rpc('eth_getTransactionCount', creator, deployed['receipt']['blockNumber']), 16)
        addresses = []
        def run(salt, payload, fail, kind, succeeds):
            nonlocal nonce
            digest = node.rpc('web3_sha3', '0x' + (PREFIX + payload).hex())
            address = '0x' + node.rpc('web3_sha3', '0xff' + creator[2:] + format(salt, '064x') + digest[2:])[-40:]
            if address not in addresses:
                addresses.append(address)
            timestamp = 1000000100 + len(rows)
            node.rpc('evm_setNextBlockTimestamp', timestamp)
            record = node.transact({'from': sender, 'to': creator,
                                    'data': calldata(selector, salt, payload, fail), 'gas': hex(10000000)})
            ident = str(len(rows))
            assert discover_create2_accounts(node, record) == {address}, kind
            row = node.observe(record, ident)
            row['deployment'] = observe_accounts(node, record, creator, addresses)
            assert row['status'] == ('ok' if succeeds else 'revert'), kind
            observed = {a['address']: a for a in row['deployment']['accounts']}[address]
            if succeeds:
                nonce += 1
                assert row['data'] == '0x' + address[2:].rjust(64, '0')
                assert observed['code'] == '0x' + payload.hex()
                assert observed['nonce'] == 1 and observed['balance'] == 0
            elif kind == 'rollback':
                assert observed['code'] == '0x' and observed['nonce'] == 0 and observed['balance'] == 0
            assert row['deployment']['creator']['nonce'] == nonce, kind
            rows.append(row)
            plans.append(sorted(addresses))
            cases.append({'id': ident, 'kind': kind, 'length': len(payload), 'address': address,
                          'transactionHash': record['receipt']['transactionHash']})
            transactions.append({'id': ident, 'sender': sender, 'target': creator, 'value': '0x0',
                                 'data': record['transaction']['data'], 'timestamp': timestamp,
                                 'blockNumber': int(record['receipt']['blockNumber'], 16)})
        for length in (0, 1, 31, 32, 33, 63, 64, 65):
            payload = bytes((i * 17) % 256 for i in range(length))
            salt = length + 1
            run(salt, payload, True, 'rollback', False)
            run(salt, payload, False, 'success', True)
            run(salt, payload, False, 'collision', False)
        run(1000, b'\xef\x00', False, 'forbidden-prefix', False)
        write_json(out / 'provenance.json', {'scope': 'real-EVM source only; not A/B/C',
                   'node': node.provenance, 'solcSha256': hashlib.sha256(SOLC.read_bytes()).hexdigest(),
                   'sourceSha256': hashlib.sha256(fixture.read_bytes()).hexdigest()})
    ids = [row['id'] for row in rows]
    # Calibrate discovery/replay using the real source bytecode on all adapters.
    # These are source clones, not Denote and compiled-model implementations.
    adapters = {route: DeploymentSequenceAdapter(out / ('source-replay-' + route),
                ['0x' + evm['bytecode']['object']], creator) for route in ROUTES}
    replay = replay_deployment_routes(transactions, adapters)
    assert not replay['divergences']
    for route in ROUTES:
        assert replay['observations'][route] == rows
    write_json(out / 'source-replay.json', {'scope': 'all adapters use source bytecode; not A/B/C', **replay})
    traces = {route: copy.deepcopy(rows) for route in ROUTES}
    assert not compare_deployment_sequences(ids, traces, plans)
    # Actual source observations, independently altered in a synthetic route.
    for key, category in [('code', 'code'), ('nonce', 'accountNonce'), ('balance', 'accountBalance')]:
        mutant = copy.deepcopy(traces)
        account = mutant['model'][1]['deployment']['accounts'][0]
        account[key] = '0xff' if key == 'code' else account[key] + 1
        differences = compare_deployment_sequences(ids, mutant, plans)
        assert differences[0]['signature'] == ((category, False, False, True),)
        controls.append({'mutation': key, 'detected': True, 'scope': 'comparator only'})
    for key, category in [('nonce', 'creatorNonce'), ('balance', 'creatorBalance')]:
        mutant = copy.deepcopy(traces)
        mutant['model'][1]['deployment']['creator'][key] += 1
        differences = compare_deployment_sequences(ids, mutant, plans)
        assert differences[0]['signature'] == ((category, False, False, True),)
        controls.append({'mutation': 'creator-' + key, 'detected': True, 'scope': 'comparator only'})
    for kind in ('missing-account', 'missing-deployment', 'duplicate', 'boolean-nonce', 'missing-code', 'dropped-plan'):
        mutant, plan = copy.deepcopy(traces), copy.deepcopy(plans)
        row = mutant['model'][1]
        if kind == 'missing-account': row['deployment']['accounts'].pop()
        elif kind == 'missing-deployment': del row['deployment']
        elif kind == 'duplicate': row['deployment']['accounts'].append(copy.deepcopy(row['deployment']['accounts'][0]))
        elif kind == 'boolean-nonce': row['deployment']['creator']['nonce'] = True
        elif kind == 'missing-code': del row['deployment']['accounts'][0]['code']
        else: plan[1] = []
        try:
            compare_deployment_sequences(ids, mutant, plan)
        except HarnessError:
            controls.append({'rejection': kind, 'rejected': True})
        else:
            raise AssertionError('incomplete observation accepted: ' + kind)
    # Replay stability checks use copies of genuine observations; these are
    # harness controls, not an executable importer/model mutation campaign.
    for kind in ('return-drift', 'creator-drift', 'code-drift', 'missing-replay-account'):
        class ChangedReplay:
            def __init__(self, change=False):
                self.calls = 0
                self.change = change
            def __call__(self, unused_transactions, unused_slots, unused_accounts):
                self.calls += 1
                result = copy.deepcopy(rows)
                if self.change and self.calls == 2:
                    row = result[1]
                    if kind == 'return-drift': row['data'] = '0x'
                    elif kind == 'creator-drift': row['deployment']['creator']['nonce'] += 1
                    elif kind == 'code-drift': row['deployment']['accounts'][0]['code'] = '0xff'
                    else: row['deployment']['accounts'].pop()
                return result
        try:
            replay_deployment_routes(transactions, {route: ChangedReplay(route == 'model') for route in ROUTES})
        except HarnessError:
            controls.append({'rejection': kind, 'rejected': True, 'scope': 'replay harness only'})
        else:
            raise AssertionError('unstable replay accepted: ' + kind)
    write_json(out / 'observations.json', {'scope': 'source only', 'cases': cases, 'observations': rows,
                                         'accountPlan': plans, 'transactions': transactions})
    write_json(out / 'controls.json', controls)
    write_json(out / 'complete.json', {'scope': 'source-only deployment instrument and comparator controls',
                                      'transactions': len(rows), 'controls': len(controls), 'exit': 0})
    print(f'Deployment source instrument: {len(rows)} transactions, {len(controls)} controls; no A/B/C claim')


if __name__ == '__main__':
    main()
