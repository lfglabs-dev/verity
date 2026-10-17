from pathlib import Path
import argparse,hashlib,json,os,subprocess
from .engine import command
root=Path(__file__).resolve().parents[2]
parser=argparse.ArgumentParser(description='Executable typed Access refusal mutations')
parser.add_argument('--output',type=Path,default=root/'.lake/typed-access-mutations')
args=parser.parse_args();job=args.output.resolve();job.mkdir(parents=True,exist_ok=False)
command(['lake','build','Compiler.SolidityImport.Access','Contracts.SolidityImportSmoke.TypedAccessChecks'],cwd=root,timeout=1800,log=job/'build.log')
source=root/'Compiler/SolidityImport/Access.lean'; original=source.read_text()
finish=original.split('def finishAccessOutcome',1)[1].split('theorem finishAccessOutcome_interpretationError',1)[0]
runner=original.split('def runFunction',1)[1].split('/-- `field[keys]',1)[0]
defs='import Compiler.SolidityImport.Import\nimport Compiler.SolidityImport.Access\nopen Compiler.CompilationModel Compiler.CompilationModel.Denote\nnamespace TypedAccessMutation\ndef finishAccessOutcome'+finish+'def runFunction'+runner+'\nend TypedAccessMutation\n'
prelude='open Compiler.CompilationModel Compiler.CompilationModel.Denote\nopen TypedAccessMutation\n'
observe='private def observe (r : Except String (Option (List Nat))) : IO Unit :=\n  match r with\n  | .error message => IO.println s!"error:{message}"\n  | .ok none => IO.println "evm-failure"\n  | .ok (some words) => IO.println s!"success:{words.length}"\n'
cases=[
 ('refusal-as-revert','| .interpretationError message => .error message','| .interpretationError message => if message.length = 0 then .ok none else .ok none',
 'def main : IO Unit := observe (finishAccessOutcome (.interpretationError "precise refusal"))'),
 ('void-as-revert','.ok (some (state.observedReturnWords.getD []))','.ok state.observedReturnWords',
 'def main : IO Unit := observe (finishAccessOutcome (.continue { world := Verity.defaultState, bindings := [] }))'),
 ('nonzero-gas-accepted','if context.opcode.gas = 0 then .ok none','if context.opcode.gas = context.opcode.gas then .ok none',
 'def main : IO Unit := observe (finishAccessOutcome (.exceptional { world := Verity.defaultState, bindings := [], executionContext := some { opcode := { gas := 1, depth := 0, isStatic := false }, warm := fun _ => false } }))'),
 ('unknown-function-accepted','| none => .error s!"unknown imported function: {name}"','| none => if name.length = 0 then .ok none else .ok none',
 'private def oracle : DenoteOracle := ⟨fun _ _ => 0, fun _ _ _ => 0⟩\nprivate def model : CompilationModel := { name := "Empty", fields := [], constructor := none, functions := [] }\ndef main : IO Unit := observe (runFunction oracle model "missing" Verity.defaultState [])')]
expected=['error:precise refusal','success:0','error:Denote exceptional exit has nonzero terminal gas','error:unknown imported function: missing']
manifest={str(p.relative_to(root)):hashlib.sha256(p.read_bytes()).hexdigest() for p in [source,root/'Contracts/SolidityImportSmoke/TypedAccessChecks.lean',root/'Contracts/SolidityImportSmoke/TypedAccessFixture.sol',Path(__file__).resolve(),root/'.lake/build/lib/lean/Compiler/SolidityImport/Access.olean']}
lean=str(Path(os.environ['LEAN_SYSROOT'])/'bin/lean') if os.environ.get('LAKE_OVERRIDE_LEAN')=='true' and os.environ.get('LEAN_SYSROOT') else 'lean'
fixture=(root/'Contracts/SolidityImportSmoke/TypedAccessChecks.lean').read_text()
fixture='\n'.join(line for line in fixture.splitlines() if not line.startswith('import '))
fixture=fixture.replace('runFunction oracle creationModel','TypedAccessMutation.runFunction oracle creationModel').replace('finishAccessOutcome (','TypedAccessMutation.finishAccessOutcome (')
fixture=fixture.replace('def main : IO Unit := SolidityImportSmoke.TypedAccessChecks.runChecks','def main : IO Unit := do\n  try\n    SolidityImportSmoke.TypedAccessChecks.runChecks\n    IO.println "PASS"\n  catch error => IO.println s!"FAIL:{error}"')
def run(name,text):
 assert all(hashlib.sha256((root/p).read_bytes()).hexdigest()==h for p,h in manifest.items())
 p=job/(name+'.lean');p.write_text(text)
 with (job/(name+'.log')).open('w') as log:
  result=subprocess.run(['lake','env',lean,'--run',str(p)],stdout=log,stderr=subprocess.STDOUT,timeout=180,cwd=root)
 output=(job/(name+'.log')).read_text().splitlines()
 assert result.returncode==0,(name,result.returncode,output)
 return output
positive=run('permanent-positive',defs+fixture)
assert positive==['typed access precise refusals and generated wrappers passed','PASS'],positive
rows=[]
for (name,old,new,witness),want in zip(cases,expected):
 assert defs.count(old)==1,(name,defs.count(old))
 base=run(name+'-baseline',defs+prelude+observe+witness)
 assert base==[want],(name,base)
 mutant_defs=defs.replace(old,new)
 smoke=run(name+'-permanent-smoke',mutant_defs+fixture)
 assert len(smoke)==1 and smoke[0].startswith('FAIL:'),(name,smoke)
 mutated=mutant_defs+prelude+observe+witness
 result=run(name+'-mutant',mutated)
 assert result==['evm-failure'],(name,result)
 replay=run(name+'-replay',mutated)
 assert replay==result
 rows.append({'name':name,'baseline':base,'mutant':result,'replay':replay,'minimal':'single outcome or lookup; no removable transaction prefix'})
assert all(hashlib.sha256((root/p).read_bytes()).hexdigest()==h for p,h in manifest.items())
(job/'success.json').write_text(json.dumps({'rows':rows,'sources':manifest,'scope':'Access semantic component witnesses only; not generated-wrapper importer mutations or full release'},indent=2))
