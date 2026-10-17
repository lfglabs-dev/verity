"""Actual payload validator mutations, with finite witnesses and exact replay.

These witnesses detect incorrect rejection of finite messages and bypassing old
validation. They do not materialize strings near the 2**256 address boundary;
that unmaterializable boundary is covered by the quantified Lean fixture.
"""
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
from .engine import command

MUTANTS = {
    'payload-extent-rejects-finite': ('requirePayloadFitsWord',
        '≤ Compiler.Constants.evmModulus', '≤ 0', 'fit'),
    'payload-node-polarity': ('requirePayloadOverflow',
        '=> !requirePayloadFitsWord message', '=> requirePayloadFitsWord message', 'nested'),
    'payload-deep-gate-polarity': ('validateRequirePayloads',
        'if Stmt.anyDeepList requirePayloadOverflow body then',
        'if !Stmt.anyDeepList requirePayloadOverflow body then', 'nested'),
    'payload-function-rejects-finite': ('validateFunctionSpec',
        'validateRequirePayloads s!"function \'{spec.name}\'" spec.body',
        'throw "incorrect function payload rejection"', 'function'),
    'payload-constructor-rejects-finite': ('validateConstructorSpec',
        'validateRequirePayloads "constructor" spec.body',
        'throw s!"incorrect constructor payload rejection {spec.body.length}"', 'constructor'),
    'payload-function-base-bypassed': ('validateFunctionSpec',
        'validateFunctionSpecBase spec', 'pure ()', 'invalid-function'),
    'payload-constructor-base-bypassed': ('validateConstructorSpec',
        'validateConstructorSpecBase ctor', 'pure ()', 'invalid-constructor'),
}


def main():
    root = Path(__file__).resolve().parents[2]
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, required=True)
    job = parser.parse_args().output.resolve()
    job.mkdir(parents=True, exist_ok=False)
    payload = root / 'Compiler/CompilationModel/RequirePayloadValidation.lean'
    validation = root / 'Compiler/CompilationModel/Validation.lean'
    fixture = root / 'Contracts/SolidityImportSmoke/RequirePayloadValidationChecks.lean'
    files = [payload, validation, fixture, Path(__file__).resolve()]
    identity = {str(p.relative_to(root)): hashlib.sha256(p.read_bytes()).hexdigest() for p in files}

    def unchanged():
        return identity == {str(p.relative_to(root)): hashlib.sha256(p.read_bytes()).hexdigest() for p in files}

    command(['lake', 'build', 'Contracts.SolidityImportSmoke.RequirePayloadValidationChecks'],
            cwd=root, timeout=1800, log=job / 'build.log')
    bodies = {}
    names = ['requirePayloadFitsWord', 'requirePayloadOverflow', 'validateRequirePayloads',
             'validateFunctionSpec', 'validateConstructorSpec']
    for name in names:
        raw = (payload if name in names[:3] else validation).read_text()
        match = re.search(r'^def ' + name + r'\b', raw, re.M)
        assert match, name
        rest = raw[match.start():]
        end = re.search(r'\n(?:def |/\-|end )', rest)
        assert end, name
        bodies[name] = rest[:end.start()]
    pattern = r'\b(' + '|'.join(names) + r')\b'

    def rename(text, qualified=False):
        return re.sub(pattern, lambda m: ('PayloadMutation.' if qualified else '') + m[0] + '_mut', text)

    def implementation(parts):
        return ('import Compiler.CompilationModel.Validation\nnamespace PayloadMutation\n'
                'open Compiler.CompilationModel\n' + rename('\n\n'.join(parts[n] for n in names)) +
                '\nend PayloadMutation\n')

    runtime = rename(fixture.read_text(), qualified=True)
    runtime = '\n'.join(line for line in runtime.splitlines() if not line.startswith('import '))
    main_line = 'def main : IO Unit := SolidityImportSmoke.RequirePayloadValidationChecks.runChecks'
    assert runtime.count(main_line) == 1
    runtime = runtime.replace(main_line,
        'def main : IO Unit := do\n  try\n    SolidityImportSmoke.RequirePayloadValidationChecks.runChecks\n'
        '    IO.println "PASS"\n  catch error => IO.println s!"FAIL:{error}"')
    expressions = {
        'fit': 'requirePayloadFitsWord ""',
        'nested': 'validateRequirePayloads "nested" [.ite (.literal 1) [.forEach "i" (.literal 1) [.require (.literal 1) ""]] []]',
        'function': 'validateFunctionSpec { name := "payload", params := [], returnType := none, body := [.require (.literal 1) ""] }',
        'constructor': 'validateConstructorSpec (some { params := [], body := [.require (.literal 1) ""] })',
        'invalid-function': 'validateFunctionSpec { name := "invalid", params := [], returnType := none, body := [], isPure := true, isPayable := true }',
        'invalid-constructor': 'validateConstructorSpec (some { params := [], body := [.return (.literal 0)] })',
    }

    def minimal(kind):
        return ('open Compiler.CompilationModel\ndef main : IO Unit :=\n  IO.println (reprStr (' +
                rename(expressions[kind], qualified=True) + '))\n')

    def run(name, parts, test):
        assert unchanged(), 'campaign inputs changed'
        path = job / (name + '.lean')
        path.write_text(implementation(parts) + test)
        lean = str(Path(os.environ['LEAN_SYSROOT']) / 'bin/lean') if os.environ.get('LAKE_OVERRIDE_LEAN') == 'true' else 'lean'
        result = command(['lake', 'env', lean, '--run', str(path)], cwd=root,
                         timeout=180, log=job / (name + '.log')).splitlines()
        assert unchanged(), 'campaign inputs changed'
        return result

    assert run('positive', bodies, runtime) == [
        'Require payload extent and preserved production validation checks passed', 'PASS']
    rows = []
    for name, (definition, anchor, replacement, kind) in MUTANTS.items():
        parts = dict(bodies)
        assert parts[definition].count(anchor) == 1, name
        parts[definition] = parts[definition].replace(anchor, replacement, 1)
        failed = run(name, parts, runtime)
        assert len(failed) == 1 and failed[0].startswith('FAIL:'), (name, failed)
        test = minimal(kind)
        expected = run(name + '-baseline', bodies, test)
        actual = run(name + '-actual', parts, test)
        replay = run(name + '-replay', parts, test)
        assert len(expected) == len(actual) == 1 and expected != actual and actual == replay
        rows.append(dict(name=name, expected=expected, actual=actual, replay=replay, failed=failed))
        print(name, 'detected with independent finite witness and replay', flush=True)
    artifacts = {p.name: hashlib.sha256(p.read_bytes()).hexdigest() for p in job.glob('*.lean')}
    (job / 'success.json').write_text(json.dumps(dict(exit=0, sources_unchanged=unchanged(),
        identity=identity, artifacts=artifacts, rows=rows), indent=2))


if __name__ == '__main__':
    main()
