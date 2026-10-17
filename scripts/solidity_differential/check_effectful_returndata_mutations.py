"""Executable mutations of effectful IR returndata/revert transport.

Every mutant runs the same permanent fixture as its successful baseline;
compile/tool failures never count as semantic detection.
"""
import argparse
import hashlib
import json
import os
from pathlib import Path
from .engine import command


def main():
    root = Path(__file__).resolve().parents[2]
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, required=True)
    job = parser.parse_args().output.resolve(); job.mkdir(parents=True, exist_ok=False)
    source = root/'Compiler/Proofs/IRGeneration/IRCreationInterpreter.lean'
    fixture = root/'Contracts/SolidityImportSmoke/EffectfulReturndataChecks.lean'
    command(['lake','build','Contracts.SolidityImportSmoke.EffectfulReturndataChecks'],
            cwd=root,timeout=1800,log=job/'build.log')
    identity = {str(p.relative_to(root)):hashlib.sha256(p.read_bytes()).hexdigest()
                for p in [source,fixture,Path(__file__).resolve()]}
    defs = source.read_text().split('theorem invokeMstore_two',1)[0]
    defs = defs.replace('namespace Compiler.Proofs.IRGeneration.IRCreationInterpreter',
                        'namespace Compiler.Proofs.IRGeneration.EffectfulReturndataMutation')
    defs += '\nend Compiler.Proofs.IRGeneration.EffectfulReturndataMutation\n'
    smoke = fixture.read_text().split('private def initial',1)[1]
    smoke = 'namespace SolidityImportSmoke.EffectfulReturndataChecks\n'+ \
        'open Compiler.Yul Compiler.Proofs.IRGeneration EffectfulReturndataMutation\nopen Verity.Core.Model\nprivate def initial'+smoke
    smoke = smoke.replace('def main : IO Unit := SolidityImportSmoke.EffectfulReturndataChecks.runChecks',
        'def main : IO Unit := do\n  try\n    SolidityImportSmoke.EffectfulReturndataChecks.runChecks\n    IO.println "PASS"\n  catch error => IO.println s!"FAIL:{error}"')
    mutants = [
        ('copy-source-shift', 'copyPhysicalReturndata destination source extent',
         'copyPhysicalReturndata destination (source + 1) extent'),
        ('zero-size-edge-rejected', 'source + extent ≤ 32 * runtime.state.returndata.length',
         'source + extent < 32 * runtime.state.returndata.length'),
        ('exception-retains-gas', 'context.opcode with gas := 0',
         'context.opcode with gas := context.opcode.gas'),
        ('source-normalization-dropped', 'let source := source % Compiler.Constants.evmModulus',
         'let source := source'),
        ('revert-payload-reversed', '.revert ((List.range size).map',
         '.revert ((List.range size).reverse.map'),
        ('missing-context-becomes-revert',
         '.interpretationError "effectful IR returndata copy exceptional exit requires actual opcode context"',
         '.revert [] runtime'),
        ('terminal-payload-erased', '| .revert data runtime => .revert data runtime',
         '| .revert data runtime => .revert (if data.isEmpty then [] else []) runtime'),
    ]
    env = dict(os.environ)
    lean = str(Path(env['LEAN_SYSROOT'])/'bin/lean') if env.get('LAKE_OVERRIDE_LEAN') == 'true' else 'lean'
    def run(name, body, test=smoke):
        driver = job/(name+'.lean'); driver.write_text(body+test)
        return command(['lake','env',lean,'--run',str(driver)],cwd=root,timeout=1800,
                       log=job/(name+'.log')).splitlines()
    minimal_prefix = r"""
open Compiler.Yul Compiler.Proofs.IRGeneration EffectfulReturndataMutation
open Verity.Core.Model

def context : ExecutionContext :=
  { opcode := { gas := 19, depth := 0, isStatic := false }, warm := fun _ => false }
def initial : Runtime :=
  { state :=
      { ((IRState.initial 0).writePhysicalMemoryValue 0 0x1234) with
        returndata := [0x1234]
        executionContext := some context }
    creationContexts := [] }
def observe : Outcome Unit → IO Unit
  | .value _ next => IO.println s!"value:{(List.range 32).map (fun i => (next.state.byteMemory.readByte i).val)}"
  | .revert data _ => IO.println s!"revert:{data.map UInt8.toNat}"
  | .exceptional next => IO.println s!"exception:{next.state.executionContext.map (·.opcode.gas)}"
  | .interpretationError message => IO.println s!"refusal:{message}"
  | .stop _ => IO.println "stop"
"""
    witnesses = {
        'copy-source-shift': 'invokeReturndatacopy initial [0, 30, 2]',
        'zero-size-edge-rejected': 'invokeReturndatacopy initial [0, 32, 0]',
        'exception-retains-gas': 'invokeReturndatacopy initial [0, 33, 0]',
        'source-normalization-dropped': 'invokeReturndatacopy initial [0, Compiler.Constants.evmModulus + 30, 2]',
        'revert-payload-reversed': 'invokeRevert initial [30, 2]',
        'missing-context-becomes-revert': 'invokeReturndatacopy { initial with state := { initial.state with executionContext := none } } [0, 33, 0]',
        'terminal-payload-erased': 'execStmts 32 initial [.exprStmt (.call "revert" [.lit 30, .lit 2])]',
    }
    rows=[]
    for name,old,new in mutants:
        assert old in defs, name
        baseline = run(name+'-baseline',defs)
        assert baseline == ['effectful returndata bytes, exceptional gas, frame and terminal checks passed','PASS'],baseline
        result = run(name+'-mutant',defs.replace(old,new,1))
        assert len(result)==1 and result[0].startswith('FAIL:'),(name,result)
        minimal = minimal_prefix+'\ndef main : IO Unit := observe ('+witnesses[name]+')\n'
        expected = run(name+'-minimal-baseline',defs,minimal)
        actual = run(name+'-minimal-mutant',defs.replace(old,new,1),minimal)
        replay = run(name+'-minimal-replay',defs.replace(old,new,1),minimal)
        assert len(expected)==len(actual)==1 and expected!=actual and actual==replay,(name,expected,actual,replay)
        rows.append({'name':name,'baseline':baseline,'detected':result,
                     'expected':expected,'actual':actual,'replay':replay,
                     'minimal':'one primitive outcome or one terminal statement; no removable transaction prefix'})
    assert identity == {str(p.relative_to(root)):hashlib.sha256(p.read_bytes()).hexdigest()
                        for p in [source,fixture,Path(__file__).resolve()]}
    (job/'success.json').write_text(json.dumps({'exit':0,'rows':rows,'identity':identity,
        'scope':'Staged effectful IR semantics mutations only; no importer admission or full release evidence'},indent=2))
    print(f'{len(rows)} effectful returndata mutants detected and replayed')


if __name__ == '__main__': main()
