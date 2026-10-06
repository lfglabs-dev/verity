"""Replay adapter invoking the actual Lean Denote sequence runner."""
import hashlib
import json
import os
from pathlib import Path
import re

from .engine import HarnessError, command, write_json
from .identity import ImplementationIdentity
from .stateful import _bytes, validate_observation


def _uint(value):
    if type(value) is not int or not 0 <= value < 1 << 256:
        raise HarnessError('model adapter requires a uint256 integer')
    return str(value)


def _calldata(tx):
    """Require one identical complete payload for EVM and Denote execution."""
    data = tx.get('data')
    if not isinstance(data, str) or not re.fullmatch(r'0x[0-9a-f]*', data):
        raise HarnessError('canonical source calldata required')
    raw = bytes.fromhex(data[2:]) if len(data) % 2 == 0 else b''
    if len(raw) < 4 or (len(raw) - 4) % 32:
        raise HarnessError('stateful Denote requires word-aligned source calldata')
    words = [int.from_bytes(raw[i:i+32], 'big') for i in range(4, len(raw), 32)]
    args = tx.get('args')
    if not isinstance(args, list) or any(type(arg) is not int for arg in args) or words != args:
        raise HarnessError('source calldata differs from model argument words')
    return str(int.from_bytes(raw[:4], 'big'))


class SequenceAdapter:
    def __init__(self, directory, driver, account, initial_storage=(), identity=None, *, cached_driver=False):
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
        self.cached_driver = cached_driver
        self.cache = None

    def _cached_command(self):
        """Compile once with the real Lean toolchain, then interpret that module.

        Original implementation checks remain active. Cached source, wrapper
        and all emitted module artifacts receive their own immutable identity.
        """
        self.identity.verify()
        if hashlib.sha256(self.driver.read_bytes()).hexdigest() != self.digest:
            raise HarnessError('model driver changed before cached sequence replay')
        if self.cache is None:
            cache = self.directory / '_driver-cache'
            cache.mkdir(parents=True, exist_ok=False)
            module = 'SolidityDenoteCache' + self.digest
            source = cache / (module + '.lean')
            artifact = cache / (module + '.olean')
            source.write_bytes(self.driver.read_bytes())
            if hashlib.sha256(source.read_bytes()).hexdigest() != self.digest:
                raise HarnessError('model driver changed while preparing cached module')
            command(['lake', 'env', 'lean', '--root=' + str(cache),
                     '-o', artifact, source], log=cache / 'compile.log')
            if not artifact.is_file():
                raise HarnessError('cached Lean driver artifact missing')
            wrapper = cache / 'Replay.lean'
            wrapper.write_text('import ' + module + '\n')
            lean_path = command(['lake', 'env', 'printenv', 'LEAN_PATH']).strip()
            argv = ['lake', 'env', 'env', 'LEAN_PATH=' + str(cache) + os.pathsep + lean_path,
                    'lean', '--run', wrapper]
            paths = sorted(p for p in cache.rglob('*') if p.is_file() and p.suffix != '.log')
            stats = {str(p): ImplementationIdentity._stat(p) for p in paths}
            hashes = {str(p): hashlib.sha256(p.read_bytes()).hexdigest() for p in paths}
            self.identity.verify()
            self.cache = {'directory': cache, 'argv': argv, 'paths': paths,
                          'stats': stats, 'hashes': hashes}
            write_json(cache / 'manifest.json', {'originalDriver': str(self.driver),
                'originalDriverSha256': self.digest, 'command': list(map(str, argv)),
                'files': hashes, 'scope': 'actual Lean module; opt-in cached replay'})
        cache = self.cache
        paths = sorted(p for p in cache['directory'].rglob('*') if p.is_file()
                       and p.suffix != '.log' and p.name != 'manifest.json')
        try:
            unchanged = paths == cache['paths'] and all(
                ImplementationIdentity._stat(p) == cache['stats'][str(p)] for p in paths)
        except OSError as error:
            raise HarnessError('cached Lean driver became unavailable') from error
        if not unchanged:
            raise HarnessError('cached Lean driver changed during sequence campaign')
        return cache['argv']

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
                'args': [_uint(arg) for arg in tx['args']], 'selector': _calldata(tx),
                'sender': str(int(_bytes(tx['sender'], 20), 16)),
                'target': str(int(_bytes(tx['target'], 20), 16)),
                'value': _uint(int(tx['value'], 16)),
                'timestamp': _uint(tx['timestamp']), 'blockNumber': _uint(tx['blockNumber']),
                'observe': [[str(int(_bytes(owner, 20), 16)), str(int(_bytes(slot, 32), 16))]
                            for owner, slot in slots]})
        write_json(directory / 'input.json', {'account': str(int(self.account, 16)),
            'storage': self.initial_storage, 'transactions': converted})
        argv = (self._cached_command() if self.cached_driver else
                ['lake', 'env', 'lean', '--run', self.driver]) + [directory / 'input.json', directory / 'output.json']
        command(argv, log=directory / 'lean.log')
        self.identity.verify()
        if self.cached_driver:
            self._cached_command()
        rows = json.loads((directory / 'output.json').read_text())
        if not isinstance(rows, list) or len(rows) != len(transactions):
            raise HarnessError('model omitted transaction observations')
        for tx, row in zip(transactions, rows):
            validate_observation(row)
            if tx['id'] != row['id']:
                raise HarnessError('model transaction identity differs')
        write_json(directory / 'replay.json', {'driver': str(self.driver), 'driverSha256': self.digest,
            'command': list(map(str, argv)), 'transactions': transactions, 'slots': plan,
            'cachedDriverFiles': self.cache['hashes'] if self.cache else None})
        return rows
