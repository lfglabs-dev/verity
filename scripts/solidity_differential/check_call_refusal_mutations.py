from pathlib import Path
import argparse,hashlib,json,os,re,subprocess
from .engine import command
def main():
    root=Path(__file__).resolve().parents[2]
    parser=argparse.ArgumentParser(description="Executable checked-call refusal mutations")
    parser.add_argument('--output', type=Path, default=root/'.lake/call-refusal-mutations')
    args=parser.parse_args()
    job=args.output.resolve();job.mkdir(parents=True,exist_ok=False)
    command(['lake','build','Verity.Core.Model.DenoteFunctionCalls','Contracts.SolidityImportSmoke.CallRefusal'],
            cwd=root,timeout=1800,log=job/'build.log')
    source=root/'Verity/Core/Model/DenoteFunctionCalls.lean'
    original=source.read_text()
    # Executable copies remove proof declarations only. A compilation failure is
    # never evidence that the behavioral assertions detect a mutant.
    prefix=re.sub(r'(?ms)^theorem .*?(?=^def |^structure |^inductive |^private def |^theorem |^end Compiler\.|^/\-! ##|\Z)','',original)
    prefix=prefix.replace('Compiler.CompilationModel.DenoteFunctionCalls','Compiler.CompilationModel.DenoteFunctionCallsMutation')
    fixture=(root/'Contracts/SolidityImportSmoke/CallRefusal.lean').read_text()
    fixture=fixture.split('\n',1)[1].replace('Compiler.CompilationModel.DenoteFunctionCalls','Compiler.CompilationModel.DenoteFunctionCallsMutation')
    fixture=fixture.replace('def main : IO Unit := SolidityImportSmoke.CallRefusal.runChecks','''def main : IO Unit := do
      try
        SolidityImportSmoke.CallRefusal.runChecks
        IO.println "PASS"
      catch error => IO.println s!"FAIL:{error}"''')
    manifest={str(p.relative_to(root)):hashlib.sha256(p.read_bytes()).hexdigest()
     for d in ['Compiler','Verity','Contracts','test/CodeData']
     for p in (root/d).rglob('*') if p.suffix in {'.lean','.sol'}}
    identity={str(p.relative_to(root)):hashlib.sha256(p.read_bytes()).hexdigest() for p in
     [source,root/'Contracts/SolidityImportSmoke/CallRefusal.lean',Path(__file__).resolve(),
     root/'.lake/build/lib/lean/Verity/Core/Model/DenoteFunctionCalls.olean']}
    env=dict(os.environ)
    lean=str(Path(env['LEAN_SYSROOT'])/'bin/lean') if env.get('LAKE_OVERRIDE_LEAN')=='true' and env.get('LEAN_SYSROOT') else 'lean'
    def unchanged():
     return all(hashlib.sha256((root/p).read_bytes()).hexdigest()==h for p,h in {**manifest,**identity}.items())
    def run(name,definitions,body):
     assert unchanged()
     p=job/(name+'.lean');p.write_text(definitions+body)
     with (job/(name+'.log')).open('w') as log:
      child=subprocess.Popen(['lake','env',lean,'--run',str(p)],env=env,stdout=log,stderr=subprocess.STDOUT)
      (job/'running.json').write_text(json.dumps({'supervisor':os.getpid(),'child':child.pid,'stage':name}))
      code=child.wait()
     result={'exit':code,'driver_sha256':hashlib.sha256(p.read_bytes()).hexdigest(),'sources_unchanged':unchanged()}
     (job/(name+'.json')).write_text(json.dumps(result,indent=2))
     output=(job/(name+'.log')).read_text().splitlines()
     assert code==0 and unchanged(),(name,output[-15:])
     return output
    baseline=run('positive',prefix,fixture)
    assert baseline==['call-aware refusal propagation and atomic rollback passed','PASS'],baseline
    # Each minimal witness prints a semantic observation and exits successfully.
    prelude='''\nopen Compiler.CompilationModel Compiler.CompilationModel.Denote
    open Compiler.CompilationModel.DenoteFunctionCallsMutation
    open Compiler.CompilationModel.DenoteExternalCalls
    open Verity.MultiContract
    private def oracle : DenoteOracle := ⟨fun _ _ => 0, fun _ _ _ => 0⟩
    private def env : CallEnv := { oracle, adversary := identityAdversary, resolve := fun _ => none }
    private def creation : Stmt := .create2 "created" (.literal 0) (.literal 0) (.literal 0)
    '''
    witness_list=prelude+'''def main : IO Unit := do
      match execStmtListWithCalls env [] { world := Verity.defaultState, bindings := [] } [creation] with
      | .interpretationError message => IO.println s!"error:{message}"
      | .revert => IO.println "revert"
      | _ => IO.println "other"
    '''
    witness_finish=prelude+'''def main : IO Unit := do
      match finishFunctionExecution Verity.defaultState (.interpretationError "refusal") with
      | .error message => IO.println s!"error:{message}"
      | .ok result => IO.println s!"evm:{result.result.succeeded}"
    '''
    witness_gas=prelude+'''def main : IO Unit := do
      match finishFunctionExecution Verity.defaultState (.exceptional
        { world := Verity.defaultState, bindings := [], executionContext := some
            { opcode := { gas := 1, depth := 0, isStatic := false }, warm := fun _ => false } }) with
      | .error message => IO.println s!"error:{message}"
      | .ok result => IO.println s!"evm:{result.result.succeeded}"
    '''
    witness_transaction=prelude+'''private def model : CompilationModel :=
      { name := "Probe", fields := [{ name := "stored", ty := .uint256 }], constructor := none, functions := [] }
    private def before : MultiWorld := { accounts := [
      { address := 1, state := { Verity.defaultState with selfBalance := 10 } },
      { address := 2, state := Verity.defaultState.writeSlot 0 7 }] }
    private def compiled (body : List Stmt) : CompiledCall :=
      { env, spec := model, fn := { name := "probe", params := [], returnType := none, body },
        selector := 0, caller := 1, callee := 2,
        site := { siteId := 0, kind := .call, target := 2, value := 1, calldata := [], gas := 100 } }
    def main : IO Unit := do
      let result := denoteTransaction before [
        compiled [.setStorage "stored" (.literal 99), .stop], compiled [creation]]
      match result.control with
      | .interpretationError index message =>
          IO.println s!"error:{index}:{message}:{((lookup result.world 2).readSlot 0).val}:{(lookup result.world 1).selfBalance.val}:{result.calls.length}"
      | .callFailed index _ => IO.println s!"evm:{index}"
      | _ => IO.println "other"
    '''
    mutations=[
     ('list-refusal-becomes-revert','| .interpretationError message => .interpretationError message','| .interpretationError _ => .revert',witness_list),
     ('function-refusal-becomes-revert','| .interpretationError message => .error message','| .interpretationError _ => .ok { result := .revert [], world := initialWorld }',witness_finish),
     ('exception-accepts-nonzero-gas','if context.opcode.gas = 0 then','if context.opcode.gas ≥ 0 then',witness_gas),
     ('transaction-refusal-retains-prefix','{ control := .interpretationError index message, world := before,','{ control := .interpretationError index message, world := current,',witness_transaction),
     ('transaction-refusal-becomes-call-failure','{ control := .interpretationError index message, world := before,','{ control := .callFailed index (.revert (message.toUTF8.data.toList.take 0 |>.map UInt8.toNat)), world := before,',witness_transaction),
    ]
    results=[]
    for name,before,after,witness in mutations:
     assert prefix.count(before)==1,(name,prefix.count(before))
     mutant=prefix.replace(before,after)
     output=run(name,mutant,fixture)
     assert len(output)==1 and output[0].startswith('FAIL:'),(name,output)
     control=run(name+'-witness-control',prefix,witness)
     actual=run(name+'-witness',mutant,witness)
     assert len(control)==len(actual)==1 and control!=actual,(name,control,actual)
     replay=run(name+'-witness-replay',mutant,witness)
     assert replay==actual
     results.append({'name':name,'smoke':output,'expected':control,'actual':actual,'replayed':True})
     print(name,'detected and minimal witness independently replayed',flush=True)
    assert unchanged()
    (job/'complete.json').write_text(json.dumps({'exit':0,'positive':baseline,'mutants':results,'identity':identity,'sources':manifest,
     'scope':'Actual call-aware boundary executable component mutations; all compile/runs exit0 and every divergence independently replays a single statement, finalization, or two-call transaction witness. Not lowering mutations/EVM replay/full A-B-C/release.'},indent=2))
    print('5 checked-call boundary mutants passed',flush=True)

if __name__ == "__main__":
    main()
