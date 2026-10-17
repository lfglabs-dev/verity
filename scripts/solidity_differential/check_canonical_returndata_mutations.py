"""Semantic mutations of actual canonical IR copy and terminal transport.

Clone the production definitions, excluding unrelated proof declarations. Every
mutant must compile, fail the same permanent runtime fixture as its successful
baseline, and reproduce a distinct independently observed minimal outcome.
"""
import argparse
import hashlib
import json
import os
import re
from pathlib import Path
from .engine import command


def main():
    root = Path(__file__).resolve().parents[2]
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, required=True)
    parser.add_argument('--only', action='append')
    args = parser.parse_args()
    job = args.output.resolve(); job.mkdir(parents=True, exist_ok=False)
    source = root/'Compiler/Proofs/IRGeneration/IRInterpreter.lean'
    fixture = root/'Contracts/SolidityImportSmoke/CanonicalIRReturndataChecks.lean'
    command(['lake', 'build', 'Contracts.SolidityImportSmoke.CanonicalIRReturndataChecks'],
            cwd=root, timeout=1800, log=job/'build.log')
    paths = [source, fixture, root/'Compiler/Proofs/IRGeneration/IRRuntimeTypes.lean', Path(__file__).resolve()]
    identity = {str(p.relative_to(root)): hashlib.sha256(p.read_bytes()).hexdigest() for p in paths}
    production = source.read_text()
    measure_start = production.index('mutual\ndef exprSize')
    measures = production[measure_start:production.index('/-! ## Execution State Helpers', measure_start)]
    start = production.index('mutual\n\n/-- Evaluate a list of Yul expressions in the helper-aware')
    helpers = production[start:production.index('\nend\n', start)+5]
    start = production.index('mutual\n\n/-- Execute a single Yul statement with fuel bound.')
    ordinary = production[start:production.index('\nend -- mutual', start)+len('\nend -- mutual')]
    prefix = '''import Compiler.Proofs.IRGeneration.IRInterpreter
namespace Compiler.Proofs.IRGeneration.CanonicalReturndataMutation
open Compiler Compiler.Yul Compiler.Proofs.IRGeneration
'''
    def definitions(helper=helpers, plain=ordinary):
        return prefix + measures + helper + '\n' + plain + '\nend Compiler.Proofs.IRGeneration.CanonicalReturndataMutation\n'
    copy_definition = 'private def copy' + fixture.read_text().split('private def copy', 1)[1].split('\n\nexample', 1)[0]
    smoke = 'namespace SolidityImportSmoke.CanonicalIRReturndataChecks\nopen Compiler.Yul Compiler.Proofs.IRGeneration\n' + copy_definition + '\nprivate def initial' + fixture.read_text().split('private def initial', 1)[1]
    names = ['execIRStmtsWithInternals', 'execIRStmtWithInternals', 'execIRStmts', 'execIRStmt']
    for name in names:
        smoke = re.sub(r'\b' + name + r'\b', 'CanonicalReturndataMutation.' + name, smoke)
    smoke += '''\ndef main : IO Unit := do
  try
    SolidityImportSmoke.CanonicalIRReturndataChecks.runChecks
    IO.println "PASS"
  catch error => IO.println s!"FAIL:{error}"
'''
    copy = lambda src, size, dst=0: f'.exprStmt (.call "returndatacopy" [.lit {dst}, .lit ({src}), .lit {size}])'
    cases = [
        ('ordinary-source-shift', 'ordinary', 'state.copyPhysicalReturndata dst src size', 'state.copyPhysicalReturndata dst (src + 1) size', copy('30', 2)),
        ('helper-source-shift', 'helpers', "state'.copyPhysicalReturndata dst src size", "state'.copyPhysicalReturndata dst (src + 1) size", copy('30', 2)),
        ('ordinary-zero-size-edge', 'ordinary', 'src + size ≤ 32 * state.returndata.length', 'src + size < 32 * state.returndata.length', copy('32', 0)),
        ('ordinary-exception-gas', 'ordinary', 'context.opcode with gas := 0', 'context.opcode with gas := context.opcode.gas', copy('33', 0)),
        ('helper-exception-gas', 'helpers', 'context.opcode with gas := 0', 'context.opcode with gas := context.opcode.gas', copy('33', 0)),
        ('ordinary-normalization-dropped', 'ordinary', 'let src := src % Compiler.Constants.evmModulus', 'let src := src', copy('Compiler.Constants.evmModulus + 30', 2)),
        ('helper-normalization-dropped', 'helpers', 'let src := src % Compiler.Constants.evmModulus', 'let src := src', copy('Compiler.Constants.evmModulus + 30', 2)),
        ('ordinary-missing-context-revert', 'ordinary', '| none => .interpretationError\n                      "returndata copy exceptional exit requires actual opcode context"', '| none => .revert state', copy('33', 0)),
        ('helper-missing-context-revert', 'helpers', '| none => .interpretationError\n                        "returndata copy exceptional exit requires actual opcode context"', "| none => .revert state'", copy('33', 0)),
        ('ordinary-terminal-exception-erased', 'ordinary', '| .exceptional s => .exceptional s', '| .exceptional s => .revert s', copy('33', 0)),
        ('helper-callee-capture-erased', 'helpers', '| .revert finalState =>\n            .revert (restoreCallerVars callerState finalState)', '| .revert _ =>\n            .revert callerState', '.exprStmt (.call "capture" [])'),
    ]
    selected = [row for row in cases if not args.only or row[0] in args.only]
    assert selected and (not args.only or set(args.only) <= {row[0] for row in cases})
    env = dict(os.environ)
    lean = str(Path(env['LEAN_SYSROOT'])/'bin/lean') if env.get('LAKE_OVERRIDE_LEAN') == 'true' else 'lean'
    def run(name, body, test=smoke):
        path = job/(name+'.lean'); path.write_text(body+test)
        return command(['lake', 'env', lean, '--run', str(path)], cwd=root, timeout=1800,
                       log=job/(name+'.log')).splitlines()
    minimal = '''open Compiler.Yul Compiler.Proofs.IRGeneration
private def context : Verity.Core.Model.ExecutionContext :=
  { opcode := { gas := 19, depth := 2, isStatic := false }, warm := fun _ => false }
private def initial : IRState :=
  { ((IRState.initial 0).writePhysicalMemoryValue 0 0x1234) with
    returndata := [0x1234], executionContext := some context, vars := [("outer", 7)] }
private def contract : Compiler.IRContract :=
  { name := "Minimal", deploy := [], functions := [], usesMapping := false
    internalFunctions := [.funcDef "capture" [] []
      [.exprStmt (.call "mstore" [.lit 0, .lit 0x9876]),
        .exprStmt (.call "revert" [.lit 30, .lit 2])]] }
private def observe : IRExecResult → IO Unit
  | .continue next => IO.println s!"copy:{(List.range 32).map (fun i => (next.byteMemory.readByte i).val)}"
  | .exceptional next => IO.println s!"exception:{next.executionContext.map (·.opcode.gas)}"
  | .revert next => IO.println s!"revert:{next.revertBytes.map (List.map UInt8.toNat)}"
  | .interpretationError message => IO.println s!"refusal:{message}"
  | .stop _ => IO.println "stop"
  | .return value _ => IO.println s!"return:{value}"
private def externalResult : IRExecResultWithInternals → IRExecResult
  | .continue next => .continue next
  | .exceptional next => .exceptional next
  | .interpretationError message => .interpretationError message
  | .revert next => .revert next
  | .stop next => .stop next
  | .return value next => .return value next
  | .leave _ => .interpretationError "leave"
'''
    rows=[]
    for name, region, old, new, stmt in selected:
        original = ordinary if region == 'ordinary' else helpers
        assert original.count(old) == 1, (name, original.count(old))
        changed = original.replace(old, new, 1)
        mutant = definitions(plain=changed) if region == 'ordinary' else definitions(helper=changed)
        baseline = run(name+'-baseline', definitions())
        assert baseline == ['canonical IR copy bytes, context, refusal, suffix and helper capture checks passed', 'PASS'], baseline
        detected = run(name+'-mutant', mutant)
        assert len(detected)==1 and detected[0].startswith('FAIL:'), (name, detected)
        state = '{ initial with executionContext := none }' if 'missing-context' in name else 'initial'
        expression = f'CanonicalReturndataMutation.execIRStmts 128 ({state}) [{stmt}]'
        if region == 'helpers':
            expression = f'externalResult (CanonicalReturndataMutation.execIRStmtsWithInternals contract 128 ({state}) [{stmt}])'
        witness = minimal + '\ndef main : IO Unit := observe ('+expression+')\n'
        expected = run(name+'-minimal-baseline', definitions(), witness)
        actual = run(name+'-minimal-mutant', mutant, witness)
        replay = run(name+'-minimal-replay', mutant, witness)
        assert len(expected)==len(actual)==1 and expected!=actual and actual==replay, (name, expected, actual, replay)
        rows.append({'name':name, 'baseline':baseline, 'detected':detected, 'expected':expected,
                     'actual':actual, 'replay':replay, 'minimal':'one actual canonical terminal/copy statement'})
    assert identity == {str(p.relative_to(root)):hashlib.sha256(p.read_bytes()).hexdigest() for p in paths}
    (job/'success.json').write_text(json.dumps({'exit':0, 'rows':rows, 'identity':identity,
        'scope':'Actual canonical IR component semantic mutations; no whole imported-contract certificate'}, indent=2))
    print(f'{len(rows)} canonical IR returndata mutants detected and independently replayed')


if __name__ == '__main__': main()
