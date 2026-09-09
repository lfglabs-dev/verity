#!/usr/bin/env python3
"""Focused proof-only Vault acceptance checks; all mutations are in a disposable copy.

Prerequisite: lake build SolidityVault and the pinned .lake/solidity-import/solc.
Runs no bytecode compiler and writes no generated model Lean source.
"""
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parents[1]
ENV = dict(os.environ, PATH=f"{Path.home()}/.elan/bin:{Path.home()}/.local/bin:" + os.environ['PATH'])


def check(ok, message):
    if not ok:
        raise AssertionError(message)
    print('PASS ' + message, flush=True)


def run(root, args, success=True, contains=None):
    p = subprocess.run(args, cwd=root, env=ENV, text=True, capture_output=True, timeout=180)
    out = p.stdout + p.stderr
    if (p.returncode == 0) != success or (contains and contains not in out) or 'PANIC' in out:
        raise AssertionError(f'{args}: exit {p.returncode}\n{out}')
    return out


def main():
    with tempfile.TemporaryDirectory(prefix='verity-vault-check-') as directory:
        root = Path(directory)
        # Copy mutable build outputs (never hardlink); share only prebuilt dependencies.
        for name in ('Verity', 'Contracts/SolidityVault', 'scripts', 'examples/solidity'):
            shutil.copytree(ROOT / name, root / name)
        for name in ('lakefile.lean', 'lake-manifest.json', 'lean-toolchain'):
            shutil.copy2(ROOT / name, root / name)
        for name in ('build', 'solidity-import'):
            shutil.copytree(ROOT / '.lake' / name, root / '.lake' / name)
        (root / '.lake/packages').symlink_to(ROOT / '.lake/packages', target_is_directory=True)
        source = root / 'examples/solidity/Vault.sol'
        original = source.read_bytes()
        stamp = source.stat()
        frontend = root / 'scripts/solidity_contract.py'
        frontend_original = frontend.read_bytes()
        compiler = root / '.lake/solidity-import/solc'
        compiler_original = compiler.read_bytes()
        lean_sources = set(root.rglob('*.lean'))
        def edit(data):
            source.write_bytes(data)
            os.utime(source, ns=(stamp.st_atime_ns, stamp.st_mtime_ns))
        def build(success=True, contains=None):
            return run(root, ['lake', 'build', 'SolidityVault'], success, contains)
        def model(success=True, contains=None):
            return run(root, ['python3', str(frontend), str(source)], success, contains)
        def artifacts():
            return {str(p.relative_to(root)): (p.stat().st_mtime_ns, hashlib.sha256(p.read_bytes()).hexdigest())
                    for p in (root / '.lake/build/lib/lean/Contracts/SolidityVault').glob('*.olean')}
        def caches():
            return {p.name: (p.stat().st_mtime_ns, p.read_bytes()) for p in compiler.parent.glob('*.json')}
        build()
        check(True, 'baseline lake build SolidityVault')
        proof = root / 'Contracts/SolidityVault/Proof.lean'
        theorem_names = re.findall(r'^theorem\s+(\w+)', proof.read_text(), re.M)
        audit = run(root, ['lake', 'env', 'lean', str(proof)])
        entries = re.findall(r"'Contracts.SolidityVault.(\w+)' depends on axioms: \[([^\]]*)\]", audit)
        check(set(theorem_names) == {name for name, _ in entries}, 'every theorem appears in actual #print axioms output')
        axioms = {a.strip() for _, values in entries for a in values.split(',') if a.strip()}
        check(axioms <= {'propext', 'Quot.sound', 'Classical.choice'}, 'no project axioms or sorryAx: ' + ', '.join(sorted(axioms)))
        before, cached = artifacts(), caches()
        first = model()
        build()
        check(before == artifacts(), 'unchanged Lake rebuild reuses all Vault oleans')
        check(first == model() and cached == caches(), 'unchanged frontend reuses identical AST cache without rewriting')
        cache_probe = """import runpy, subprocess, sys
original = subprocess.Popen
class Guard(subprocess.Popen):
    def __init__(self, args, *a, **kw):
        assert '--standard-json' not in args, 'unexpected solc compilation on cache hit'
        super().__init__(args, *a, **kw)
subprocess.Popen = Guard
sys.argv = sys.argv[1:]
runpy.run_path(sys.argv[0], run_name='__main__')
"""
        check(run(root, ['python3', '-c', cache_probe, str(frontend), str(source)]) == first,
              'cached frontend does not invoke solc --standard-json (subprocess guard)')
        # Mutate compiler AST only in memory; exercise the same schema gate as main.
        ast_probe = """import copy, importlib.util, json, pathlib, sys
spec = importlib.util.spec_from_file_location('frontend', sys.argv[1])
m = importlib.util.module_from_spec(spec)
spec.loader.exec_module(m)
records = [json.loads(p.read_text()) for p in pathlib.Path(sys.argv[2]).glob('*.json')]
ast = next(r['output']['sources'][m.SOURCE]['ast'] for r in records
           if r['output']['sources'][m.SOURCE]['ast']['nodes'][-1]['name'] == 'Vault')
def need(ok, n, why):
    if not ok: raise ValueError(why)
m.validate_ast(ast, need)  # existing structured documentation is legitimate
for mutation in ('unknown child', 'altered block', 'metadata child'):
    changed = copy.deepcopy(ast)
    contract = next(n for n in changed['nodes'] if n['nodeType'] == 'ContractDefinition')
    f = next(n for n in contract['nodes'] if n['nodeType'] == 'FunctionDefinition')
    if mutation == 'unknown child': f['body']['unexpectedExecutable'] = copy.deepcopy(f['body']['statements'][0])
    elif mutation == 'altered block': f['body']['nodeType'] = 'UncheckedBlock'
    else: contract['documentation']['unexpectedExecutable'] = copy.deepcopy(f['body'])
    try: m.validate_ast(changed, need)
    except ValueError: print('rejected ' + mutation)
    else: raise AssertionError('accepted ' + mutation)
"""
        probe = run(root, ['python3', '-c', ast_probe, str(frontend), str(compiler.parent)])
        check(all('rejected ' + name in probe for name in ('unknown child', 'altered block', 'metadata child')),
              'closed recursive AST schema rejects unknown executable children and altered body kind; accepts documentation')
        # Even the registered source must remain inside the canonical package root.
        with tempfile.TemporaryDirectory(prefix='verity-vault-outside-') as outside:
            escaped = Path(outside) / 'Vault.sol'
            escaped.write_bytes(original)
            source.unlink()
            source.symlink_to(escaped)
            try:
                model(False, 'source outside package')
                check(True, 'registered-source symlink escape rejected in temporary sandbox')
            finally:
                source.unlink()
                edit(original)
        baseline_model = json.loads(first)
        edit(original.replace(b'assets', b'depositAmount'))
        model()
        build()
        check(True, 'parameter rename and references preserve existing proofs')
        edit(original)
        build()
        for name, old, new in (
            ('deposit behavior', b'totalSupply += assets;', b'totalSupply = assets;'),
            ('getter behavior', b'return shareBalances[account];', b'return totalAssets;'),
        ):
            check(original.count(old) == 1, name + ' mutation has one source target')
            before = artifacts()
            edit(original.replace(old, new))
            changed_model = json.loads(model())
            check(changed_model['functions'] != baseline_model['functions'], name + ' changes accepted AST behavior')
            out = build(False, 'Contracts.SolidityVault.Proof')
            check('unsolved goals' in out or 'Type mismatch' in out or 'type mismatch' in out,
                  name + ' preserved-mtime source edit rebuilds and breaks existing proof')
            check(before != artifacts(), name + ' refreshes dependent oleans')
            edit(original)
            build()
        for name, old, new, diagnostic in (
            ('contract layout at', b'contract Vault {', b'contract Vault layout at 100 {', 'layout at'),
            ('initializer', b'uint256 public totalAssets;', b'uint256 public totalAssets = 1;', 'initializer'),
            ('unchecked block', b'totalAssets += assets;', b'unchecked { totalAssets += assets; }', 'UncheckedBlock'),
            ('loop', b'totalAssets += assets;', b'while (assets < totalAssets) { totalAssets += assets; }', 'WhileStatement'),
            ('second contract', b'contract Vault {', b'contract Other {}\ncontract Vault {', 'exactly one'),
            ('multiplication', b'totalAssets += assets;', b'totalAssets = totalAssets * assets;', 'unsupported binary'),
        ):
            edit(original.replace(old, new))
            output = model(False, diagnostic)
            check(re.search(r'examples/solidity/Vault.sol:\d+:\d+:', output) is not None,
                  name + ' rejected with source location')
        # Exercise an import failure through Lake as well as the frontend.
        build(False, 'unsupported binary')
        check(True, 'unsupported source cannot reuse prior successful Lake artifact')
        edit(original)
        build()
        before = artifacts()
        frontend.write_bytes(frontend_original + b'\n# acceptance invalidation probe\n')
        build()
        check(before != artifacts(), 'Python importer content change invalidates Vault oleans')
        check(json.loads(model())['digest'] != baseline_model['digest'], 'importer change updates sourceDigest')
        frontend.write_bytes(frontend_original)
        build()
        lean_importer = root / 'Verity/Solidity.lean'
        lean_original = lean_importer.read_bytes()
        try:
            lean_importer.write_bytes(lean_original + b'\n-- acceptance translation identity probe\n')
            check(json.loads(model())['digest'] != baseline_model['digest'],
                  'Lean translation implementation change updates sourceDigest')
            before = artifacts()
            build()
            check(before != artifacts(), 'Lean importer change invalidates Vault oleans')
        finally:
            lean_importer.write_bytes(lean_original)
        build()
        before_cache = caches()
        frontend.write_bytes(frontend_original.replace(b"optimizer={'enabled': False}", b"optimizer={'enabled': True}"))
        build()
        check(before_cache.keys() != caches().keys(), 'compiler settings change creates a distinct AST cache entry')
        frontend.write_bytes(frontend_original)
        build()
        policy = root / 'lakefile.lean'
        policy_original = policy.read_bytes()
        before = artifacts()
        policy.write_bytes(policy_original + b'\n-- acceptance build-policy probe\n')
        build()
        check(before != artifacts(), 'build-policy content change invalidates Vault oleans')
        policy.write_bytes(policy_original)
        build()
        # Appended data preserves executable format but violates the pinned binary hash.
        compiler_stamp = compiler.stat()
        compiler.write_bytes(compiler_original + b'\nacceptance-check\n')
        os.utime(compiler, ns=(compiler_stamp.st_atime_ns, compiler_stamp.st_mtime_ns))
        build(False, 'compiler checksum mismatch')
        check(True, 'compiler content change invalidates Lake and fails closed')
        compiler.write_bytes(compiler_original)
        build()
        check(set(root.rglob('*.lean')) == lean_sources, 'no generated model .lean files')
        check(source.read_bytes() == original and frontend.read_bytes() == frontend_original,
              'temporary source and importer restored; final baseline build passes')
        print(f'PASS all Vault acceptance checks ({len(theorem_names)} audited theorems)', flush=True)


if __name__ == '__main__':
    main()
