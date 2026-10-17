"""Mutate actual six-entry Source context/oracle/cursor forwarding definitions."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
from .engine import command

ENTRIES = ('interpretFunction', 'interpretConstructor', 'interpretContract',
           'interpretFunctionWithHelpers', 'interpretConstructorWithHelpers',
           'interpretContractWithHelpers')


def main():
    root = Path(__file__).resolve().parents[2]
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, required=True)
    job = parser.parse_args().output.resolve()
    job.mkdir(parents=True, exist_ok=False)
    source = root / 'Compiler/Proofs/IRGeneration/SourceSemantics.lean'
    fixture = root / 'Contracts/SolidityImportSmoke/SourcePublicContextChecks.lean'
    files = [source, fixture, Path(__file__).resolve()]
    identity = {str(p.relative_to(root)): hashlib.sha256(p.read_bytes()).hexdigest() for p in files}
    def unchanged():
        return identity == {str(p.relative_to(root)): hashlib.sha256(p.read_bytes()).hexdigest() for p in files}
    command(['lake', 'build', 'Contracts.SolidityImportSmoke.SourcePublicContextChecks'],
            cwd=root, timeout=1800, log=job / 'build.log')
    raw = source.read_text()
    bodies = {}
    for name in ENTRIES:
        start = re.search(r'^def ' + name + r'\b', raw, re.M).start()
        rest = raw[start:]
        end = re.search(r'\n(?:def |theorem |--|/\-|mutual)', rest)
        assert end, name
        bodies[name] = rest[:end.start()]
    pattern = r'\b(' + '|'.join(ENTRIES) + r')\b'
    def rename(text, qualified=False):
        return re.sub(pattern, lambda m: ('PublicContextMutation.' if qualified else '') + m[0] + '_mut', text)
    def implementation(parts):
        return ('import Compiler.Proofs.IRGeneration.SourceSemantics\n'
                'namespace PublicContextMutation\n'
                'open Compiler.CompilationModel Compiler.Proofs.IRGeneration SourceSemantics\n' +
                rename('\n\n'.join(parts[name] for name in ENTRIES)) + '\nend PublicContextMutation\n')
    runtime = rename(fixture.read_text(), qualified=True)
    runtime = '\n'.join(line for line in runtime.splitlines() if not line.startswith('import '))
    baseline_main = 'def main : IO Unit := SolidityImportSmoke.SourcePublicContextChecks.runChecks'
    assert runtime.count(baseline_main) == 1
    runtime = runtime.replace(baseline_main,
        'def main : IO Unit := do\n  try\n    SolidityImportSmoke.SourcePublicContextChecks.runChecks\n'
        '    IO.println "PASS"\n  catch error => IO.println s!"FAIL:{error}"')
    prefix = runtime.split('private def checkException', 1)[0]
    calls = {
        'interpretFunction': 'model probe tx world oracle',
        'interpretConstructor': 'model ({ params := [], body := probe.body } : ConstructorSpec) tx world oracle',
        'interpretContract': 'model [7] tx world oracle',
        'interpretFunctionWithHelpers': 'model 8 probe tx world oracle',
        'interpretConstructorWithHelpers': 'model 8 ({ params := [], body := probe.body } : ConstructorSpec) tx world oracle',
        'interpretContractWithHelpers': 'model [7] 8 tx world oracle',
    }
    def minimal(name, kind):
        call = 'PublicContextMutation.' + name + '_mut ' + calls[name]
        setup = ''
        if kind != 'context':
            setup = '''  let probe : FunctionSpec := { probe with body :=
    [.externalCallBind ["receipt"] "oracle" [],
     .require (.eq (.localVar "receipt") (.literal 103)) "wrong external cursor", .stop] }
  let model := { model with functions := [probe] }
'''
        return (prefix + 'def minimal : IO Unit := do\n' + setup +
                '  let result := ' + call + '\n    (executionContext := some context) (externalCallIndex := 3)\n'
                '  IO.println s!"{result.success}:{result.exceptionalContext.map (·.opcode.gas)}:{result.exceptionalContext.map (·.opcode.depth)}:{result.interpretationError}:{result.finalStorage 0}"\n'
                'end SolidityImportSmoke.SourcePublicContextChecks\n'
                'def main : IO Unit := SolidityImportSmoke.SourcePublicContextChecks.minimal\n')
    def run(name, parts, test):
        assert unchanged(), 'source changed during campaign'
        path = job / (name + '.lean')
        path.write_text(implementation(parts) + test)
        lean = str(Path(os.environ['LEAN_SYSROOT']) / 'bin/lean') if os.environ.get('LAKE_OVERRIDE_LEAN') == 'true' else 'lean'
        result = command(['lake', 'env', lean, '--run', str(path)], cwd=root,
                         timeout=180, log=job / (name + '.log')).splitlines()
        assert unchanged(), 'source changed during campaign'
        return result
    assert run('positive', bodies, runtime) == [
        'Source six public entry context, cursor, refusal and rollback checks passed', 'PASS']
    rows = []
    for entry in ENTRIES:
        for kind in ('context', 'cursor', 'oracle'):
            body = bodies[entry]
            if entry in ('interpretContract', 'interpretContractWithHelpers'):
                before = 'externalCallOracle executionContext externalCallIndex'
                replacement = {
                    'context': 'externalCallOracle (if executionContext.isSome then none else none) externalCallIndex',
                    'cursor': 'externalCallOracle executionContext (if externalCallIndex == 0 then 0 else 0)',
                    'oracle': '(fun index => { externalCallOracle index with succeeded := false }) executionContext externalCallIndex',
                }[kind]
            else:
                before, replacement = {
                    'context': ('executionContext := executionContext',
                                'executionContext := if executionContext.isSome then none else none'),
                    'cursor': ('externalCallIndex := externalCallIndex',
                               'externalCallIndex := if externalCallIndex == 0 then 0 else 0'),
                    'oracle': ('externalCallOracle := externalCallOracle',
                               'externalCallOracle := fun index => { externalCallOracle index with succeeded := false }'),
                }[kind]
            assert body.count(before) == 1, (entry, kind)
            parts = dict(bodies)
            parts[entry] = body.replace(before, replacement, 1)
            name = f'source-public-{entry}-{kind}-erased'
            failed = run(name, parts, runtime)
            assert len(failed) == 1 and failed[0].startswith('FAIL:'), (name, failed)
            test = minimal(entry, kind)
            expected = run(name + '-baseline', bodies, test)
            actual = run(name + '-actual', parts, test)
            replay = run(name + '-replay', parts, test)
            assert len(expected) == len(actual) == 1 and expected != actual and actual == replay
            rows.append(dict(name=name, expected=expected, actual=actual, replay=replay, failed=failed))
            print(name, 'detected and independently replayed', flush=True)
    artifacts = {p.name: hashlib.sha256(p.read_bytes()).hexdigest() for p in job.glob('*.lean')}
    (job / 'success.json').write_text(json.dumps(dict(exit=0, sources_unchanged=unchanged(),
        identity=identity, artifacts=artifacts, rows=rows), indent=2))


if __name__ == '__main__':
    main()
