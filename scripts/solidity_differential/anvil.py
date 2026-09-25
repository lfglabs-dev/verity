"""Owned local Foundry node for genuine, separately committed EVM transactions."""
from __future__ import annotations

import json
from pathlib import Path
import socket
import subprocess
import time
from urllib.error import URLError
from urllib.request import Request, urlopen

from .engine import HarnessError
from .stateful import validate_observation


class Anvil:
    def __init__(self, directory, hardfork='osaka'):
        self.directory = Path(directory)
        self.hardfork = hardfork
        self.process = None
        self.log = None
        self.counter = 0

    def __enter__(self):
        self.directory.mkdir(parents=True, exist_ok=True)
        with socket.socket() as sock:
            sock.bind(('127.0.0.1', 0))
            port = sock.getsockname()[1]
        self.url = f'http://127.0.0.1:{port}'
        self.log = (self.directory / 'anvil.log').open('w')
        argv = ['anvil', '--host', '127.0.0.1', '--port', str(port), '--hardfork', self.hardfork,
                '--timestamp', '1000000000', '--chain-id', '31337', '--steps-tracing', '--quiet']
        try:
            self.process = subprocess.Popen(argv, stdout=self.log, stderr=subprocess.STDOUT)
            deadline = time.monotonic() + 10
            while self.process.poll() is None and time.monotonic() < deadline:
                try:
                    if self.rpc('eth_chainId') != '0x7a69':
                        raise HarnessError('unexpected local chain identity')
                    self.provenance = {
                        'version': subprocess.check_output(['anvil', '--version'], text=True, timeout=10).strip(),
                        'arguments': argv, 'hardfork': self.hardfork, 'chainId': 31337,
                        'genesisTimestamp': 1000000000,
                    }
                    (self.directory / 'node.json').write_text(json.dumps(self.provenance, indent=2) + '\n')
                    return self
                except (URLError, TimeoutError):
                    time.sleep(0.05)
            raise HarnessError('owned Anvil node failed to start; see anvil.log')
        except BaseException:
            self.__exit__(None, None, None)
            raise

    def __exit__(self, *unused):
        if self.process is not None and self.process.poll() is None:
            self.process.terminate()
            try:
                self.process.wait(timeout=5)
            except subprocess.TimeoutExpired:
                self.process.kill()
                self.process.wait(timeout=5)
        if self.log is not None:
            self.log.close()

    def rpc(self, method, *params):
        self.counter += 1
        request = {'jsonrpc': '2.0', 'id': self.counter, 'method': method, 'params': list(params)}
        with urlopen(Request(self.url, json.dumps(request).encode(),
                             {'Content-Type': 'application/json'}), timeout=30) as response:
            result = json.load(response)
        if not isinstance(result, dict) or result.get('id') != self.counter or 'error' in result or 'result' not in result:
            raise HarnessError(f'RPC {method} failed: {result}')
        return result['result']

    def transact(self, transaction):
        """Mine one real transaction; retain receipts and traces for inspection."""
        txhash = self.rpc('eth_sendTransaction', transaction)
        deadline = time.monotonic() + 10
        receipt = None
        while receipt is None and time.monotonic() < deadline:
            receipt = self.rpc('eth_getTransactionReceipt', txhash)
            if receipt is None:
                time.sleep(0.05)
        if not isinstance(receipt, dict) or receipt.get('transactionHash') != txhash:
            raise HarnessError('missing mined transaction receipt')
        call = self.rpc('debug_traceTransaction', txhash, {'tracer': 'callTracer'})
        prestate = self.rpc('debug_traceTransaction', txhash, {'tracer': 'prestateTracer'})
        record = {'transaction': transaction, 'receipt': receipt, 'call': call, 'prestate': prestate}
        (self.directory / f'{txhash}.json').write_text(json.dumps(record, indent=2) + '\n')
        return record

    def observe(self, record, ident, slots=()):
        """Read exact post-state at the mined block, including rolled-back slots."""
        receipt, call, prestate = (record[k] for k in ('receipt', 'call', 'prestate'))
        status = receipt.get('status')
        if status not in ('0x0', '0x1') or not isinstance(call, dict) or not isinstance(prestate, dict):
            raise HarnessError('invalid execution trace')
        if status == '0x0' and call.get('error') != 'execution reverted':
            raise HarnessError('exceptional halt or resource failure is not a Solidity revert')
        if status == '0x1' and 'error' in call:
            raise HarnessError('receipt and trace status disagree')
        touched = set()
        for account, state in prestate.items():
            if not isinstance(state, dict) or not isinstance(state.get('storage', {}), dict):
                raise HarnessError('invalid prestate storage trace')
            touched.update((account, slot) for slot in state.get('storage', {}))
        observed = touched | set(map(tuple, slots))
        storage = [[account, slot, self.rpc('eth_getStorageAt', account, slot, receipt['blockNumber'])]
                   for account, slot in sorted(observed)]
        events = []
        for log in receipt['logs']:
            if log.get('removed') is not False:
                raise HarnessError('unconfirmed or removed transaction log')
            events.append({'address': log['address'], 'topics': log['topics'], 'data': log['data']})
        row = {'id': ident, 'status': 'ok' if status == '0x1' else 'revert',
               'data': call.get('output', '0x'), 'touched': [list(k) for k in sorted(touched)],
               'storage': storage, 'events': events}
        validate_observation(row)
        return row


class SequenceAdapter:
    """Replay a pinned deployment and transaction sequence on a fresh owned node.

    Addresses are concrete and identical across routes (same deployer/nonces).
    Callers supply route-specific calldata and explicit block timestamps; this
    initial storage is installed verbatim from the fixture. ABI values and
    emitted events are observed without normalization.
    """
    def __init__(self, directory, bytecodes, initial_storage=(), calldata_key='data'):
        self.directory = Path(directory)
        self.bytecodes = tuple(bytecodes)
        self.initial_storage = tuple(tuple(row) for row in initial_storage)
        self.calldata_key = calldata_key
        self.runs = 0

    def __call__(self, transactions, plan):
        if len(transactions) != len(plan):
            raise HarnessError('slot plan does not cover the transaction sequence')
        directory = self.directory / str(self.runs)
        self.runs += 1
        observations, receipts = [], []
        with Anvil(directory) as node:
            deployer = node.rpc('eth_accounts')[0]
            for code in self.bytecodes:
                deployment = node.transact({'from': deployer, 'data': code, 'gas': hex(10000000)})
                if deployment['receipt']['status'] != '0x1':
                    raise HarnessError('fixture deployment failed')
            for account, slot, value in self.initial_storage:
                node.rpc('anvil_setStorageAt', account, slot, value)
            for transaction, slots in zip(transactions, plan):
                # Require exact environments. Silently filling these from the
                # host clock would make block-dependent imports incomparable.
                required = ('id', 'sender', 'target', self.calldata_key, 'value', 'timestamp', 'blockNumber')
                if any(key not in transaction for key in required):
                    raise HarnessError('incomplete transaction environment')
                timestamp, number = transaction['timestamp'], transaction['blockNumber']
                if type(timestamp) is not int or type(number) is not int or timestamp < 0:
                    raise HarnessError('invalid transaction block environment')
                next_number = int(node.rpc('eth_blockNumber'), 16) + 1
                if number < next_number:
                    raise HarnessError('requested block number precedes transaction position')
                # A reduced sequence preserves each surviving transaction's
                # block environment. Fill deleted positions with empty blocks.
                if number > next_number:
                    node.rpc('anvil_mine', hex(number - next_number), '0x0')
                node.rpc('evm_setNextBlockTimestamp', timestamp)
                request = {'from': transaction['sender'], 'to': transaction['target'],
                           'data': transaction[self.calldata_key], 'value': transaction['value'],
                           'gas': hex(10000000)}
                result = node.transact(request)
                block = node.rpc('eth_getBlockByHash', result['receipt']['blockHash'], False)
                if int(block['timestamp'], 16) != timestamp or int(block['number'], 16) != number:
                    raise HarnessError('mined transaction environment changed')
                observations.append(node.observe(result, transaction['id'], slots))
                receipts.append({'id': transaction['id'], 'transactionHash': result['receipt']['transactionHash']})
        (directory / 'sequence.json').write_text(json.dumps(
            {'bytecodes': self.bytecodes, 'initialStorage': self.initial_storage,
             'calldataKey': self.calldata_key, 'node': node.provenance,
             'transactions': transactions, 'receipts': receipts,
             'slots': plan, 'observations': observations}, indent=2) + '\n')
        return observations
