"""Fail closed if the local Lean implementation changes during a campaign."""
import hashlib
from pathlib import Path

from .engine import HarnessError, command


class ImplementationIdentity:
    """Hash sources/artifacts once; reject any inventory or filesystem change.

    Stat checks include inode and ctime, so ordinary edits, replacements and
    rebuilds invalidate the snapshot even when size or mtime are preserved.
    This guards concurrent local work, not a malicious filesystem/kernel.
    """
    def __init__(self, driver, extra_inputs=()):
        self.workspace = Path.cwd().resolve()
        self.driver = Path(driver).resolve()
        self.extra_inputs = tuple(Path(path).resolve() for path in extra_inputs)
        self.toolchain = Path(command(['lake', 'env', 'lean', '--print-prefix']).strip())
        self.paths = self._inventory()
        self.stats = {str(p): self._stat(p) for p in self.paths}
        self.manifest = {
            'revision': command(['git', 'rev-parse', 'HEAD']).strip(),
            'files': {str(p): hashlib.sha256(p.read_bytes()).hexdigest() for p in self.paths}}
        self.verify()

    @staticmethod
    def _stat(path):
        s = path.stat()
        return (s.st_dev, s.st_ino, s.st_size, s.st_mtime_ns, s.st_ctime_ns)

    def _inventory(self):
        files = {self.driver, *self.extra_inputs}
        files.update((self.workspace / 'scripts/solidity_differential').rglob('*.py'))
        for name in ('lean', 'lake'):
            binary = self.toolchain / 'bin' / name
            if binary.exists():
                files.add(binary)
        for name in ('Compiler', 'Verity', 'Contracts'):
            files.update((self.workspace / name).rglob('*.lean'))
        for name in ('lean-toolchain', 'lake-manifest.json', 'lakefile.lean', 'lakefile.toml'):
            p = self.workspace / name
            if p.exists():
                files.add(p)
        roots = [self.workspace / '.lake/build/lib', self.toolchain / 'lib/lean']
        roots.extend((self.workspace / '.lake/packages').glob('*/.lake/build/lib'))
        for root in roots:
            files.update(p for p in root.rglob('*') if p.is_file() and
                         (p.suffix in ('.olean', '.ilean', '.so', '.dylib', '.a') or
                          p.name.endswith(('.olean.private', '.olean.server'))))
        return sorted(files)

    def verify(self):
        try:
            current = self._inventory()
            unchanged = current == self.paths and all(
                self._stat(p) == self.stats[str(p)] for p in current)
        except OSError as exc:
            raise HarnessError('Lean implementation snapshot became unavailable') from exc
        if not unchanged:
            raise HarnessError('Lean implementation changed during sequence campaign')
