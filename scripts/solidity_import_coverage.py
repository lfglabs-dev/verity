#!/usr/bin/env python3
"""Measure actual Solidity import attempts over an immutable source corpus.

The inventory uses each project's pinned Solidity compiler. Import attempts use
Verity's own solidity_import command, never an independent acceptance heuristic.
Infrastructure errors remain unknown and cannot count as rejections or successes.
"""
from __future__ import annotations

import argparse
import base64
import io
import tarfile
from collections import Counter
import hashlib
import json
from pathlib import Path
import platform
import re
import subprocess
import sys
import urllib.request

ROOT = Path(__file__).resolve().parents[1]
MANIFEST = ROOT / 'scripts/solidity_import_corpus/manifest.json'


class MeasurementError(RuntimeError):
    pass


def run(args, *, cwd=ROOT, stdin=None, timeout=180):
    try:
        return subprocess.run(list(map(str, args)), cwd=cwd, input=stdin,
                              text=True, capture_output=True, timeout=timeout)
    except (OSError, subprocess.TimeoutExpired) as exc:
        raise MeasurementError(str(exc)) from exc


def checked(args, **kwargs):
    result = run(args, **kwargs)
    if result.returncode:
        raise MeasurementError(f'{args[0]} exited {result.returncode}: '
                               + (result.stdout + result.stderr)[-4000:])
    return result.stdout


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def implementation_hashes(workspace):
    files = [p for name in ('Compiler', 'Verity') for p in (workspace / name).rglob('*.lean')]
    files += [workspace / name for name in ('lean-toolchain', 'lake-manifest.json', 'lakefile.lean')]
    return {p.relative_to(workspace).as_posix(): sha(p) for p in sorted(files)}


def write_json(path, value):
    path.write_text(json.dumps(value, indent=2) + '\n')


def checkout(project, cache, fetch):
    path = cache / 'sources' / project['id']
    revision = project['commit']
    if not re.fullmatch(r'[0-9a-f]{40}', revision):
        raise MeasurementError('source revision must be a full commit SHA')
    if not (path / '.git').exists():
        if not fetch:
            raise MeasurementError(f'missing corpus checkout: {path}; run with --fetch')
        path.mkdir(parents=True, exist_ok=True)
        checked(['git', 'init', '-q', path])
        checked(['git', 'remote', 'add', 'origin', project['repository']], cwd=path)
        checked(['git', 'fetch', '--depth', '1', 'origin', revision], cwd=path, timeout=300)
        checked(['git', 'checkout', '--detach', 'FETCH_HEAD'], cwd=path)
    if checked(['git', 'rev-parse', 'HEAD'], cwd=path).strip() != revision:
        raise MeasurementError(f'wrong corpus revision: {path}')
    if checked(['git', 'status', '--porcelain', '--untracked-files=all'], cwd=path).strip():
        raise MeasurementError(f'dirty corpus checkout: {path}')
    return path


def dependencies(project, source_root, cache, fetch):
    """Install inert, integrity-pinned npm source archives; never run npm scripts."""
    for pin in project.get('dependencies', []):
        algorithm, digest = pin['integrity'].split('-', 1)
        if algorithm != 'sha512':
            raise MeasurementError('dependency requires SHA-512 integrity pin')
        archive = cache / 'archives' / (hashlib.sha256(pin['integrity'].encode()).hexdigest() + '.tgz')
        if not archive.exists():
            if not fetch:
                raise MeasurementError('missing dependency archive: ' + pin['package'])
            with urllib.request.urlopen(pin['url'], timeout=120) as response:
                data = response.read()
            if base64.b64encode(hashlib.sha512(data).digest()).decode() != digest:
                raise MeasurementError('dependency download checksum mismatch')
            archive.parent.mkdir(parents=True, exist_ok=True)
            archive.write_bytes(data)
        data = archive.read_bytes()
        if base64.b64encode(hashlib.sha512(data).digest()).decode() != digest:
            raise MeasurementError('dependency archive checksum mismatch')
        files = {}
        with tarfile.open(fileobj=io.BytesIO(data), mode='r:gz') as tar:
            for member in tar.getmembers():
                path = Path(member.name)
                if path.is_absolute() or '..' in path.parts or path.parts[0] != 'package':
                    raise MeasurementError('unsafe dependency archive path')
                if member.isdir():
                    continue
                if not member.isfile():
                    raise MeasurementError('dependency archive links are not supported')
                relative = Path(*path.parts[1:])
                if relative in files:
                    raise MeasurementError('duplicate dependency archive path')
                files[relative] = tar.extractfile(member).read()
        target = source_root / 'node_modules' / pin['package']
        if target.exists():
            observed = {p.relative_to(target) for p in target.rglob('*') if p.is_file()}
            if any(p.is_symlink() for p in target.rglob('*')) or target.is_symlink():
                raise MeasurementError('dependency checkout contains symlinks')
            if observed != set(files) or any((target / p).read_bytes() != data for p, data in files.items()):
                raise MeasurementError('dependency checkout differs from pinned archive: ' + pin['package'])
        else:
            for path, data in files.items():
                dest = target / path
                dest.parent.mkdir(parents=True, exist_ok=True)
                dest.write_bytes(data)


def compiler(version, manifest, cache, fetch):
    host = ('macosx-amd64' if sys.platform == 'darwin' else
            'linux-amd64' if sys.platform.startswith('linux') and
            platform.machine() in ('x86_64', 'amd64') else None)
    if host is None:
        raise MeasurementError('no pinned inventory compiler for this platform')
    pin = manifest['compilers'][version][host]
    path = cache / 'compilers' / ('solc-' + version)
    if not path.exists():
        if not fetch:
            raise MeasurementError(f'missing inventory compiler: {path}; run with --fetch')
        path.parent.mkdir(parents=True, exist_ok=True)
        url = 'https://raw.githubusercontent.com/ethereum/solc-bin/gh-pages/' + host + '/' + pin['path']
        with urllib.request.urlopen(url, timeout=120) as response:
            data = response.read()
        if hashlib.sha256(data).hexdigest() != pin['sha256']:
            raise MeasurementError('inventory compiler download checksum mismatch')
        path.write_bytes(data)
        path.chmod(0o755)
    if sha(path) != pin['sha256']:
        raise MeasurementError('inventory compiler checksum mismatch')
    return path


def position(source, src):
    start = int(src.split(':')[0])
    before = source.encode()[:start]
    return {'line': before.count(b'\n') + 1,
            'column': len(before.rsplit(b'\n', 1)[-1]) + 1}


def spelling(node, source):
    """Preserve source type spellings; only normalize Solidity's uint/int aliases."""
    canonical = node.get('typeDescriptions', {}).get('typeString')
    if canonical:
        for prefix in ('struct ', 'contract ', 'enum '):
            if canonical.startswith(prefix):
                canonical = canonical[len(prefix):]
        for suffix in (' storage pointer', ' storage ref', ' memory', ' calldata', ' storage'):
            if canonical.endswith(suffix):
                canonical = canonical[:-len(suffix)]
        return canonical
    kind = node['nodeType']
    if kind == 'ElementaryTypeName':
        return {'uint': 'uint256', 'int': 'int256', 'byte': 'bytes1'}.get(node['name'], node['name'])
    if kind == 'UserDefinedTypeName':
        return node.get('namePath') or node.get('name') or node['pathNode']['name']
    if kind == 'ArrayTypeName':
        length = node.get('length')
        if length is None:
            suffix = ''
        else:
            start, size, _ = map(int, length['src'].split(':'))
            suffix = source.encode()[start:start + size].decode()
        return spelling(node['baseType'], source) + '[' + suffix + ']'
    # The importer does not accept function/mapping type roots. Retain their
    # exact source spelling so the declaration is reported rather than lost.
    start, size, _ = map(int, node['src'].split(':'))
    return source.encode()[start:start + size].decode()


def inventory(project, target, source_root, solc, out):
    entry = target['entry']
    source = (source_root / entry).read_text()
    version = tuple(map(int, project['inventory_solc'].split('.')))
    if version >= (0, 8, 0):
        sources = {entry: {'content': source}}
        command = [solc, '--base-path', source_root, '--standard-json']
    else:
        # Legacy solc has no base-path option. Supply the self-contained core
        # production tree inline; do not pull in test-only npm dependencies.
        sources = {p.relative_to(source_root).as_posix(): {'content': p.read_text()}
                   for p in sorted((source_root / 'contracts').rglob('*.sol'))
                   if 'test' not in p.relative_to(source_root).parts}
        command = [solc, '--standard-json']
    remapping_file = source_root / 'remappings.txt'
    remappings = [line.strip() for line in remapping_file.read_text().splitlines()
                  if line.strip() and not line.lstrip().startswith('#')] if remapping_file.exists() else []
    request = {'language': 'Solidity', 'sources': sources,
               'settings': {'remappings': remappings, 'outputSelection': {'*': {'': ['ast']}}}}
    write_json(out / 'inventory-input.json', request)
    result = json.loads(checked(command, stdin=json.dumps(request)))
    write_json(out / 'inventory-output.json', result)
    errors = [e['formattedMessage'] for e in result.get('errors', []) if e['severity'] == 'error']
    if errors:
        raise MeasurementError('inventory compiler rejected source: ' + '\n'.join(errors))
    definitions = {}
    for filename, unit in result['sources'].items():
        path = (source_root / filename).resolve()
        if not path.is_relative_to(source_root.resolve()):
            raise MeasurementError('inventory source escapes pinned project')
        for node in unit['ast']['nodes']:
            if node['nodeType'] == 'ContractDefinition':
                definitions[node['id']] = (filename, node)
    contracts = [n for filename, n in definitions.values() if filename == entry
                 and n['name'] == target['contract']]
    if len(contracts) != 1:
        raise MeasurementError('inventory contract missing or ambiguous')
    functions, seen = [], set()
    # solc supplies C3 order. Most-derived implementations win on a signature;
    # private helpers keep their declaring-contract identity.
    for contract_id in contracts[0]['linearizedBaseContracts']:
        filename, declaration = definitions[contract_id]
        text = (source_root / filename).read_text()
        for node in declaration['nodes']:
            if node['nodeType'] != 'FunctionDefinition' or node.get('kind') == 'constructor':
                continue
            if node.get('body') is None:
                continue
            types = [spelling(p['typeName'], text) for p in node['parameters']['parameters']]
            label = node['name'] or node.get('kind', 'function')
            signature = label + '(' + ','.join(types) + ')'
            identity = (node.get('kind', 'function'), signature,
                        declaration['name'] if node['visibility'] == 'private' else '')
            if identity in seen:
                continue
            seen.add(identity)
            functions.append({'name': node['name'], 'kind': node.get('kind', 'function'),
                              'types': types, 'visibility': node['visibility'],
                              'signature': signature, 'declaring_contract': declaration['name'],
                              'file': filename, **position(text, node['src'])})
    if not functions:
        raise MeasurementError('empty function inventory')
    return functions


DIAGNOSTIC = re.compile(r'(?P<file>[^\s:]+\.sol):(?P<line>\d+):(?P<column>\d+): '
                        r'(?P<construct>[^:\n]+): \[solidity-import:unsupported\] (?P<reason>[^\n]+)')


def classify(code, output):
    match = DIAGNOSTIC.search(output)
    if code == 0:
        if 'COVERAGE_IMPORT_OK' not in output:
            return {'status': 'error', 'error': 'missing successful elaboration marker'}
        return {'status': 'importable'}
    if match:
        result = match.groupdict()
        result['line'], result['column'] = int(result['line']), int(result['column'])
        return {'status': 'rejected', 'blocker': result}
    # A pragma rejected by the importer's pinned solc is a source blocker,
    # unlike compiler crashes or absent tools. Keep the real solc location.
    if 'Source file requires different compiler version' in output:
        loc = re.search(r'--> ([^\n]+\.sol):(\d+):(\d+):', output)
        if loc:
            return {'status': 'rejected', 'blocker': {
                'file': loc[1], 'line': int(loc[2]), 'column': int(loc[3]),
                'construct': 'PragmaDirective',
                'reason': 'source version incompatible with importer solc 0.8.34'}}
    # Compiler, kernel, missing-source, timeout, syntax and tool failures are
    # not unsupported-construct evidence. Keep the complete log as an artifact.
    return {'status': 'error', 'error': f'process exit {code}: ' + output[-2000:]}


def probe(function, target, source_root, out, workspace, timeout):
    # Escape Lean identifiers, including array type spellings, as one name.
    def ident(value):
        if '»' in value or '«' in value or '\n' in value:
            raise MeasurementError('unrepresentable Lean identifier')
        return '«' + value + '»'
    name = function['name']
    if function['kind'] != 'function' or not name:
        return {'status': 'rejected', 'blocker': {
            'file': function['file'], 'line': function['line'], 'column': function['column'],
            'construct': function['kind'], 'reason': 'solidity_import selects named functions only'}}
    driver = out / 'Probe.lean'
    driver.write_text('import Compiler.SolidityImport.Import\n'
        + f'solidity_import measured from {json.dumps(str(source_root))} entry {json.dumps(target["entry"])}\n'
        + '  using { evmVersion := "osaka", viaIR := true, optimizerRuns := some 466, bytecodeHash := "none" }\n'
        + f'  contract {ident(target["contract"])}\n'
        + f'  function {ident(name)}({", ".join(ident(t) for t in function["types"])})\n'
        + '#eval show IO Unit from do\n'
        + '  let some root := measured.report.includedFunctions.head? | throw (IO.userError "missing root report")\n'
        + f'  if root.contract != {json.dumps(function["declaring_contract"])} || root.name != {json.dumps(name)} then\n'
        + '    IO.println "COVERAGE_WRONG_ROOT"\n'
        + '  else IO.println "COVERAGE_IMPORT_OK"\n')
    # The generated file must live beneath the workspace lakefile: the importer
    # determines its package root from the importing Lean source location.
    if not driver.resolve().is_relative_to(workspace):
        raise MeasurementError('report output must be inside the Lean workspace')
    result = run(['lake', 'env', 'lean', driver], cwd=workspace, timeout=timeout)
    output = result.stdout + result.stderr
    (out / 'import.log').write_text(output)
    classified = classify(result.returncode, output)
    root_closure = re.search(r'^closure: ([^\n]+)', output, re.MULTILINE)
    wrong_root = (result.returncode == 0 and 'COVERAGE_WRONG_ROOT' in output)
    wrong_failure = (classified['status'] == 'rejected' and root_closure is not None
                     and root_closure[1].split(' -> ')[0] != function['declaring_contract'] + '.' + name)
    if wrong_root or wrong_failure:
        return {'status': 'rejected', 'blocker': {
            'file': function['file'], 'line': function['line'], 'column': function['column'],
            'construct': 'Inheritance', 'reason': 'probe selected a different declaring contract'}}
    if (classified['status'] == 'error' and result.returncode == 1
            and function['declaring_contract'] != target['contract']
            and f'no function {target["contract"]}.{name}(' in output):
        return {'status': 'rejected', 'blocker': {
            'file': function['file'], 'line': function['line'], 'column': function['column'],
            'construct': 'Inheritance', 'reason': 'importer cannot select inherited implementation'}}
    return classified


def summarize(rows):
    counts = Counter(row['status'] for row in rows)
    blockers = Counter(row['blocker']['construct'] + ': ' + row['blocker']['reason']
                       for row in rows if row['status'] == 'rejected')
    return {'functions': len(rows), 'importable': counts['importable'],
            'rejected': counts['rejected'], 'errors': counts['error'],
            'percent_importable': 100 * counts['importable'] / len(rows) if rows else None,
            'complete': not counts['error'] and bool(rows),
            'first_blocker_histogram': [{'blocker': k, 'functions': v}
                                      for k, v in sorted(blockers.items(), key=lambda p: (-p[1], p[0]))]}


def refresh_report(report):
    """Finalize a snapshot without ever treating pending inventory as complete."""
    identity = lambda c: (c['project'], c['entry'], c['contract'])
    observed = [identity(c) for c in report['contracts']]
    expected = [identity(c) for c in report['expected_contracts']]
    report['pending'] = [c for c in report['expected_contracts'] if identity(c) not in observed]
    report['summary'] = summarize([fn for c in report['contracts'] for fn in c['functions']])
    report['complete'] = (bool(expected) and len(observed) == len(set(observed))
                          and set(observed) == set(expected)
                          and all(c['summary']['complete'] for c in report['contracts']))
    if report['pending'] or any('error' in c for c in report['contracts']):
        report['summary']['percent_importable'] = None
        report['summary']['complete'] = False
    return report


def markdown(report):
    lines = ['# Solidity import coverage', '', report['scope'], '',
             'Measurement complete: ' + str(report['complete']).lower() + '.', '',
             'Pending contracts: ' + (', '.join(c['project'] + ':' + c['contract'] for c in report.get('pending', [])) or 'none') + '.', '',
             'Unknown/tool failures stay in the denominator. Percentages are lower bounds when a measurement is incomplete.', '',
             '| Contract | Imported / declared | % | Unknown |', '| --- | ---: | ---: | ---: |']
    for contract in report['contracts']:
        s = contract['summary']
        pct = 'unavailable' if s['percent_importable'] is None else f'{s["percent_importable"]:.2f}'
        lines.append(f'| {contract["project"]}:{contract["contract"]} | {s["importable"]}/{s["functions"]} | {pct} | {s["errors"]} |')
    lines += ['', '## First blocking constructs, weighted by rejected functions', '',
              'These weights count functions whose *first* rejection is the construct. They are an upper bound on immediate unlocks: further blockers may remain after its implementation.', '']
    for row in report['summary']['first_blocker_histogram']:
        lines.append(f'- {row["functions"]}: {row["blocker"]}')
    for contract in report['contracts']:
        if 'milestone_without_multicall' in contract:
            m = contract['milestone_without_multicall']
            lines += ['', f'Midnight milestone (excluding only `multicall`): {m["importable"]}/{m["functions"]}; unknown: {m["errors"]}.']
        lines += ['', '## ' + contract['project'] + ':' + contract['contract'], '']
        if 'error' in contract:
            lines += ['Measurement error: ' + contract['error'], '']
        for fn in contract['functions']:
            if fn['status'] == 'rejected':
                b = fn['blocker']
                lines.append(f'- `{fn["signature"]}`: `{b["file"]}:{b["line"]}:{b["column"]}` {b["construct"]}: {b["reason"]}')
            elif fn['status'] == 'error':
                lines.append(f'- `{fn["signature"]}`: measurement error (see JSON and import log).')
    return '\n'.join(lines) + '\n'


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--manifest', type=Path, default=MANIFEST)
    parser.add_argument('--workspace', type=Path, default=ROOT)
    parser.add_argument('--output', type=Path, default=ROOT / '.lake/solidity-import-coverage')
    parser.add_argument('--cache', type=Path, default=ROOT / '.lake/coverage')
    parser.add_argument('--fetch', action='store_true')
    parser.add_argument('--project', action='append', help='measure only named projects (recorded in report)')
    parser.add_argument('--timeout', type=int, default=120)
    args = parser.parse_args()
    workspace, output, cache = args.workspace.resolve(), args.output.resolve(), args.cache.resolve()
    output.mkdir(parents=True, exist_ok=True)
    # Replace prior-run success artifacts before any fallible setup/build work.
    write_json(output / 'coverage.json', {'schema': 1, 'complete': False, 'error': 'measurement initializing'})
    (output / 'coverage.md').write_text('# Solidity import coverage unavailable\n\nMeasurement initializing.\n')
    manifest = json.loads(args.manifest.read_text())
    projects = [p for p in manifest['projects'] if not args.project or p['id'] in args.project]
    if not projects or (args.project and set(args.project) - {p['id'] for p in projects}):
        parser.error('unknown or empty project selection')
    report = {'schema': 1, 'scope': manifest['scope'], 'manifest_sha256': sha(args.manifest),
              'selection': [p['id'] for p in projects], 'contracts': [],
              'verity_head': checked(['git', 'rev-parse', 'HEAD'], cwd=workspace).strip(),
              'measurement_script_sha256': sha(Path(__file__)),
              'expected_contracts': [{'project': p['id'], **t} for p in projects for t in p['contracts']]}
    refresh_report(report)
    write_json(output / 'coverage.json', report)
    (output / 'coverage.md').write_text(markdown(report))
    try:
        build = run(['lake', 'build', 'Compiler.SolidityImport.Import'], cwd=workspace, timeout=1800)
        (output / 'build.log').write_text(build.stdout + build.stderr)
        if build.returncode:
            raise MeasurementError(f'importer build failed ({build.returncode}); see build.log')
    except MeasurementError as exc:
        report.update({'complete': False, 'error': str(exc), 'summary': summarize([])})
        write_json(output / 'coverage.json', report)
        (output / 'coverage.md').write_text('# Solidity import coverage unavailable\n\n' + str(exc) + '\n')
        return 1
    report['implementation_sha256'] = implementation_hashes(workspace)
    for project in projects:
        for target in project['contracts']:
            item = {'project': project['id'], 'commit': project['commit'], **target, 'functions': []}
            dest = output / project['id'] / target['contract']
            dest.mkdir(parents=True, exist_ok=True)
            try:
                source_root = checkout(project, cache, args.fetch)
                dependencies(project, source_root, cache, args.fetch)
                solc = compiler(project['inventory_solc'], manifest, cache, args.fetch)
                item['source_sha256'] = sha(source_root / target['entry'])
                functions = inventory(project, target, source_root, solc, dest)
                for i, fn in enumerate(functions):
                    attempt = dest / str(i)
                    attempt.mkdir(exist_ok=True)
                    try:
                        result = probe(fn, target, source_root, attempt, workspace, args.timeout)
                    except MeasurementError as exc:
                        result = {'status': 'error', 'error': str(exc)}
                    item['functions'].append({**fn, **result})
            except (MeasurementError, OSError, ValueError, KeyError) as exc:
                item['error'] = str(exc)
            if implementation_hashes(workspace) != report['implementation_sha256']:
                item['error'] = 'importer/semantics sources changed during measurement; rerun'
                for fn in item['functions']:
                    fn.update({'status': 'error', 'error': item['error']})
            item['summary'] = summarize(item['functions'])
            if project['id'] == 'midnight':
                item['milestone_without_multicall'] = summarize(
                    [fn for fn in item['functions'] if fn['name'] != 'multicall'])
            if 'error' in item:
                item['summary']['complete'] = False
            report['contracts'].append(item)
            print(project['id'], target['contract'], item['summary'], flush=True)
            refresh_report(report)
            write_json(output / 'coverage.json', report)
            (output / 'coverage.md').write_text(markdown(report))
    return 0 if report['complete'] else 1


if __name__ == '__main__':
    raise SystemExit(main())
