"""Executable component mutations for effectful IR creation traversal.

Every mutant must compile/run successfully, fail the unchanged smoke checks,
and reproduce an independent minimal semantic witness. These are not EVM
replays, Solidity admission checks, or a complete A/B/C lowering campaign.
"""
import argparse
import hashlib
import json
import os
from pathlib import Path
import subprocess

from .engine import command


def main():
    root = Path(__file__).resolve().parents[2]
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, default=root / '.lake/ir-creation-mutations')
    job = parser.parse_args().output.resolve()
    job.mkdir(parents=True, exist_ok=False)
    command(['lake', 'build', 'Compiler.Proofs.IRGeneration.IRCreationInterpreter',
             'Contracts.SolidityImportSmoke.IRCreationChecks'],
            cwd=root, timeout=1800, log=job / 'build.log')
    source = root / 'Compiler/Proofs/IRGeneration/IRCreationInterpreter.lean'
    original = source.read_text()
    # Keep all implementation definitions; original proof failures do not count.
    definitions = original.split('theorem invokeMstore_two', 1)[0]
    definitions += '\nend Compiler.Proofs.IRGeneration.IRCreationInterpreter\n'
    definitions = definitions.replace('IRCreationInterpreter', 'IRCreationInterpreterMutation')
    fixture = (root / 'Contracts/SolidityImportSmoke/IRCreationChecks.lean').read_text()
    fixture = fixture.split('\n', 1)[1].replace('IRCreationInterpreter', 'IRCreationInterpreterMutation')
    smoke = fixture.replace('def main : IO Unit := SolidityImportSmoke.IRCreationChecks.runChecks',
                            '''def main : IO Unit := do
  try
    SolidityImportSmoke.IRCreationChecks.runChecks
    IO.println "PASS"
  catch error => IO.println s!"FAIL:{error}"''')
    witness_prefix = fixture.split('def runChecks', 1)[0]

    def witness(body):
        return (witness_prefix + 'def minimal : IO Unit := do\n' + body +
                '\nend SolidityImportSmoke.IRCreationChecks\n' +
                'def main : IO Unit := SolidityImportSmoke.IRCreationChecks.minimal\n')

    manifest = {str(p.relative_to(root)): hashlib.sha256(p.read_bytes()).hexdigest()
                for directory in ['Compiler', 'Verity', 'Contracts', 'test/CodeData']
                for p in (root / directory).rglob('*') if p.suffix in {'.lean', '.sol'}}
    identity = {str(p.relative_to(root)): hashlib.sha256(p.read_bytes()).hexdigest()
                for p in [source, Path(__file__).resolve(),
                          root / 'Contracts/SolidityImportSmoke/IRCreationChecks.lean',
                          root / '.lake/build/lib/lean/Compiler/Proofs/IRGeneration/IRCreationInterpreter.olean']}
    env = dict(os.environ)
    lean = (str(Path(env['LEAN_SYSROOT']) / 'bin/lean')
            if env.get('LAKE_OVERRIDE_LEAN') == 'true' and env.get('LEAN_SYSROOT') else 'lean')

    def unchanged():
        return all(hashlib.sha256((root / p).read_bytes()).hexdigest() == digest
                   for p, digest in {**manifest, **identity}.items())

    def run(name, implementation, driver):
        assert unchanged(), 'source/artifact identities changed'
        path = job / (name + '.lean')
        path.write_text(implementation + driver)
        with (job / (name + '.log')).open('w') as log:
            child = subprocess.Popen(['lake', 'env', lean, '--run', str(path)],
                                     cwd=root, env=env, stdout=log, stderr=subprocess.STDOUT)
            (job / 'running.json').write_text(json.dumps({
                'supervisor': os.getpid(), 'child': child.pid, 'stage': name}))
            code = child.wait()
        rows = (job / (name + '.log')).read_text().splitlines()
        result = {'exit': code, 'driver_sha256': hashlib.sha256(path.read_bytes()).hexdigest(),
                  'sources_unchanged': unchanged()}
        (job / (name + '.json')).write_text(json.dumps(result, indent=2))
        assert code == 0 and unchanged(), (name, rows[-20:])
        return rows

    positive = run('positive', definitions, smoke)
    assert positive == ['generic IR creation, ordering, scope and refusal checks passed', 'PASS'], positive
    order_before = '''(evalArgs fuel runtime rest).bind (fun tail afterTail =>
        (evalExpr fuel afterTail expr).bind (fun head afterHead =>
          .value (head :: tail) afterHead))'''
    order_after = '''(evalExpr fuel runtime expr).bind (fun head afterHead =>
        (evalArgs fuel afterHead rest).bind (fun tail afterTail =>
          .value (head :: tail) afterTail))'''
    creation_probe = witness('''  match evalExpr 64 (runtime 1000000) creation with
  | .value address next =>
      match next.state.creationWorld, next.state.executionContext with
      | some actual, some ctx => IO.println s!"VALUE:{address}:{(actual.creationAccounts 1).nonce}:{ctx.opcode.gas}"
      | _, _ => IO.println "LOST"
  | .interpretationError message => IO.println s!"ERROR:{message}"
  | _ => IO.println "TERMINAL"''')
    reuse_probe = witness('''  match evalExpr 64 (runtime 1000000) creation with
  | .value _ next =>
      match evalExpr 64 next creation with
      | .value address _ => IO.println s!"VALUE:{address}"
      | .interpretationError message => IO.println s!"ERROR:{message}"
      | _ => IO.println "TERMINAL"
  | _ => IO.println "FIRST-FAILED"''')
    exceptional_probe = witness('''  match evalExpr 64 (runtime 0) creation with
  | .exceptional _ => IO.println "EXCEPTIONAL"
  | .value address _ => IO.println s!"VALUE:{address}"
  | .interpretationError message => IO.println s!"ERROR:{message}"
  | _ => IO.println "OTHER"''')
    scope_probe = witness('''  match execStmt 64 (runtime 1000000) (.block [.let_ "local" (.lit 9)]) with
  | .value _ next => IO.println s!"LOCAL:{(next.state.getVar "local").getD 9999}"
  | _ => IO.println "TERMINAL"''')
    list_probe = witness('''  match execStmts 64 (runtime 1000000) [.let_ "first" (.lit 9)] with
  | .value _ next => IO.println s!"BINDING:{(next.state.getVar "first").getD 9999}"
  | _ => IO.println "TERMINAL"''')
    order_probe = witness('''  match evalArgs 16 (runtime 1000000) [.ident "left_missing", .ident "right_missing"] with
  | .interpretationError message => IO.println s!"ERROR:{message}"
  | _ => IO.println "OTHER"''')
    store_probe = witness('''  let initial := runtime 1000000
  let empty : Runtime := { initial with state := { initial.state with byteMemory := Memory.empty } }
  match execStmt 32 empty (.exprStmt (.call "mstore" [.lit 1, .lit 0x1234])) with
  | .value _ next => IO.println s!"WORD:{next.state.memory 1}:{next.state.byteMemory.size}"
  | _ => IO.println "TERMINAL"''')
    byte_probe = witness('''  let initial := runtime 1000000
  let empty : Runtime := { initial with state := { initial.state with byteMemory := Memory.empty } }
  match execStmt 32 empty (.exprStmt (.call "mstore8" [.lit 31, .lit 511])) with
  | .value _ next => IO.println s!"BYTE:{(next.state.byteMemory.readByte 31).val}:{next.state.byteMemory.size}"
  | _ => IO.println "TERMINAL"''')
    division_probe = witness('''  let initial := runtime 1000000
  let empty : Runtime := { initial with state := { initial.state with byteMemory := Memory.empty } }
  match execStmt 32 empty (.exprStmt (.call "mstore8" [.lit 31, .lit 256])) with
  | .value _ next => IO.println s!"BYTE:{(next.state.byteMemory.readByte 31).val}:{next.state.byteMemory.size}"
  | _ => IO.println "TERMINAL"''')
    offset_probe = witness('''  let initial := runtime 1000000
  let empty : Runtime := { initial with state := { initial.state with byteMemory := Memory.empty } }
  match execStmt 32 empty (.exprStmt (.call "mstore8"
    [.lit (Compiler.Constants.evmModulus + 31), .lit 255])) with
  | .value _ next => IO.println s!"BYTE:{(next.state.byteMemory.readByte 31).val}:{next.state.byteMemory.size}"
  | _ => IO.println "TERMINAL"''')
    mutants = [
        ('ir-mstore-drops-value',
         '(offset % Compiler.Constants.evmModulus) value) }',
         '(offset % Compiler.Constants.evmModulus) (value * 0)) }', store_probe),
        ('ir-mstore8-wrong-offset',
         'byteMemory.writeByte (offset % Compiler.Constants.evmModulus)',
         'byteMemory.writeByte (offset % Compiler.Constants.evmModulus + 1)', byte_probe),
        ('ir-mstore8-wrong-low-byte', 'value % 256', '(value + 1) % 256', byte_probe),
        ('ir-mstore8-modulo128', 'value % 256', '(value % 128) % 256', byte_probe),
        ('ir-mstore8-divides-value', 'value % 256', '(value / 2) % 256', division_probe),
        ('ir-mstore8-offset-not-normalized',
         'byteMemory.writeByte (offset % Compiler.Constants.evmModulus)',
         'byteMemory.writeByte offset', offset_probe),
        ('ir-create2-arguments-left-first', order_before, order_after, order_probe),
        ('ir-create2-drops-computed-state', '.value address { state, creationContexts := rest }',
         '.value address { state := if state.executionContext.isSome then runtime.state else runtime.state, creationContexts := rest }', creation_probe),
        ('ir-create2-reuses-context', '.value address { state, creationContexts := rest }',
         '.value address { state, creationContexts := runtime.creationContexts }', reuse_probe),
        ('ir-create2-exception-becomes-value', '.exceptional { state, creationContexts := rest }',
         '.value 0 { state, creationContexts := rest }', exceptional_probe),
        ('ir-create2-scope-leaks-locals', 'outer.vars.any (fun prior => prior.1 == binding.1)',
         'outer.vars.any (fun prior => prior.1 == binding.1) || true', scope_probe),
        ('ir-create2-list-drops-post-state',
         '(execStmt fuel runtime stmt).bind (fun _ next => execStmts fuel next rest)',
         '(execStmt fuel runtime stmt).bind (fun _ _ => execStmts fuel runtime rest)', list_probe),
    ]
    results = []
    for name, before, after, probe in mutants:
        assert definitions.count(before) == 1, (name, definitions.count(before))
        mutant = definitions.replace(before, after)
        smoke_rows = run(name, mutant, smoke)
        assert len(smoke_rows) == 1 and smoke_rows[0].startswith('FAIL:'), (name, smoke_rows)
        expected = run(name + '-witness-control', definitions, probe)
        actual = run(name + '-witness', mutant, probe)
        assert len(expected) == len(actual) == 1 and expected != actual, (name, expected, actual)
        replay = run(name + '-witness-replay', mutant, probe)
        assert replay == actual
        results.append({'name': name, 'smoke': smoke_rows, 'expected': expected,
                        'actual': actual, 'replayed': True})
        print(name, 'detected and minimal semantic witness independently replayed', flush=True)
    assert unchanged()
    (job / 'complete.json').write_text(json.dumps({
        'exit': 0, 'positive': positive, 'mutants': results, 'identity': identity,
        'sources': manifest,
        'scope': 'Twelve effectful IR component mutants, all successful compile/runs and independent minimal witness replays. Not EVM replay/translation certificate/Solidity admission/full A-B-C/release gate.'}, indent=2))
    print('12 effectful IR creation/memory mutants passed', flush=True)


if __name__ == '__main__':
    main()
