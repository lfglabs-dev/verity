"""Replay adapter invoking the actual Lean Denote sequence runner."""
import hashlib
import json
from pathlib import Path
import re

from .engine import HarnessError, command, write_json
from .identity import ImplementationIdentity
from .stateful import _bytes, validate_observation


def _uint(value):
    if type(value) is not int or not 0 <= value < 1 << 256:
        raise HarnessError('model adapter requires a uint256 integer')
    return str(value)


class SequenceAdapter:
    def __init__(self, directory, driver, account, initial_storage=(), identity=None):
        self.directory = Path(directory).resolve()
        self.driver = Path(driver).resolve()
        self.account = _bytes(account, 20)
        self.initial_storage = []
        for owner, slot, value in initial_storage:
            if _bytes(owner, 20) != self.account:
                raise HarnessError('foreign initial storage unsupported by scalar model adapter')
            self.initial_storage.append([str(int(_bytes(slot, 32), 16)),
                                         str(int(_bytes(value, 32), 16))])
        self.digest = hashlib.sha256(self.driver.read_bytes()).hexdigest()
        self.identity = identity or ImplementationIdentity(self.driver)
        self.runs = 0

    def __call__(self, transactions, plan):
        self.identity.verify()
        if len(transactions) != len(plan):
            raise HarnessError('model slot plan length differs')
        if hashlib.sha256(self.driver.read_bytes()).hexdigest() != self.digest:
            raise HarnessError('model driver changed during sequence replay')
        directory = self.directory / str(self.runs)
        directory.mkdir(parents=True, exist_ok=False)
        self.runs += 1
        converted = []
        for tx, slots in zip(transactions, plan):
            required = {'id', 'function', 'args', 'sender', 'target', 'value', 'timestamp', 'blockNumber'}
            if not isinstance(tx, dict) or not required <= tx.keys():
                raise HarnessError('incomplete model transaction')
            if not isinstance(tx['function'], str) or not isinstance(tx['args'], list):
                raise HarnessError('model function and argument array required')
            if not isinstance(tx['value'], str) or not re.fullmatch(r'0x(?:0|[1-9a-f][0-9a-f]*)', tx['value']):
                raise HarnessError('canonical transaction value quantity required')
            converted.append({'id': tx['id'], 'function': tx['function'],
                'args': [_uint(arg) for arg in tx['args']],
                'sender': str(int(_bytes(tx['sender'], 20), 16)),
                'target': str(int(_bytes(tx['target'], 20), 16)),
                'value': _uint(int(tx['value'], 16)),
                'timestamp': _uint(tx['timestamp']), 'blockNumber': _uint(tx['blockNumber']),
                'observe': [[str(int(_bytes(owner, 20), 16)), str(int(_bytes(slot, 32), 16))]
                            for owner, slot in slots]})
        write_json(directory / 'input.json', {'account': str(int(self.account, 16)),
            'storage': self.initial_storage, 'transactions': converted})
        argv = ['lake', 'env', 'lean', '--run', self.driver, directory / 'input.json', directory / 'output.json']
        command(argv, log=directory / 'lean.log')
        self.identity.verify()
        rows = json.loads((directory / 'output.json').read_text())
        if not isinstance(rows, list) or len(rows) != len(transactions):
            raise HarnessError('model omitted transaction observations')
        for tx, row in zip(transactions, rows):
            validate_observation(row)
            if tx['id'] != row['id']:
                raise HarnessError('model transaction identity differs')
        write_json(directory / 'replay.json', {'driver': str(self.driver), 'driverSha256': self.digest,
            'command': list(map(str, argv)), 'transactions': transactions, 'slots': plan})
        return rows
