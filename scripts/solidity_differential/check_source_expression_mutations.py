"""Typed expression primitive mutants, with independent single-outcome replays."""
import argparse
import hashlib
import json
from pathlib import Path
from .engine import command


def main():
    root = Path(__file__).resolve().parents[2]
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, required=True)
    job = parser.parse_args().output.resolve()
    job.mkdir(parents=True, exist_ok=False)
    command(['lake','build','Contracts.SolidityImportSmoke.SourceExpressionOutcomeChecks'],
            cwd=root,timeout=1800,log=job/'build.log')
    source = root/'Compiler/Proofs/IRGeneration/SourceExpressionOutcome.lean'
    fixture_path = root/'Contracts/SolidityImportSmoke/SourceExpressionOutcomeChecks.lean'
    definitions = source.read_text().split('theorem bind_refusal',1)[0]
    definitions += '\nend Compiler.Proofs.IRGeneration.SourceExpressionOutcome\n'
    definitions = definitions.replace('SourceExpressionOutcome','SourceExpressionMutation')
    fixture = fixture_path.read_text().split('\n',1)[1].replace('SourceExpressionOutcome','SourceExpressionMutation')
    fixture = fixture.replace('def main : IO Unit := SolidityImportSmoke.SourceExpressionMutationChecks.runChecks',
        'def main : IO Unit := do\n  try\n    SolidityImportSmoke.SourceExpressionMutationChecks.runChecks\n'
        '    IO.println "PASS"\n  catch error => IO.println s!"FAIL:{error}"')
    prefix = fixture.split('def runChecks',1)[0]
    suffix = '\nend SolidityImportSmoke.SourceExpressionMutationChecks\ndef main : IO Unit := SolidityImportSmoke.SourceExpressionMutationChecks.minimal\n'
    def probe(expression):
        return prefix + '''def minimal : IO Unit := do
  let result : Result Nat := '''+expression+'''
  match result with
  | .value value state => IO.println s!"VALUE:{value}:{(state.world.memory 96).val}:{state.bindings.length}:{state.observedReturnWords}"
  | .revert => IO.println "REVERT"
  | .revertWithData data => IO.println s!"REVERTBYTES:{data}"
  | .halt _ => IO.println "HALT"
  | .interpretationError message => IO.println s!"ERROR:{message}"
  | .exceptional _ => IO.println "EXCEPTIONAL"
'''+suffix
    error_probe = probe('ofHelperBody caller (.interpretationError "refused")')
    bind_probe = probe('Result.bind (.interpretationError "refused" : Result Nat) (fun _ state => .value 1 state)')
    exception_probe = probe('ofHelperBody caller (.exceptional caller)')
    return_probe = probe('ofHelperBody caller (.return 7 { caller with world := caller.world.writePhysicalMemoryValue 96 9, bindings := [("local", 8), ("second", 2)] })')
    list_probe = prefix+'''def minimal : IO Unit := do
  let eval : RuntimeState → Expr → Result Nat := fun state expr =>
    match expr with
    | .literal value => .value value { state with world := state.world.writeSlot 1 value }
    | _ => .value (state.world.readSlot 1).val state
  match evalList eval caller [.literal 23, .storage "probe"] with
  | .value values _ => IO.println s!"VALUES:{values}"
  | _ => IO.println "TERMINAL"
'''+suffix
    assign_probe = prefix+'''def minimal : IO Unit := do
  match assign "result" (.interpretationError "refused") with
  | .interpretationError message => IO.println s!"ERROR:{message}"
  | .revert => IO.println "REVERT"
  | .revertWithData data => IO.println s!"REVERTBYTES:{data}"
  | _ => IO.println "OTHER"
'''+suffix
    mutants = [
        ('expression-bind-refusal-as-revert',
         '| .interpretationError message => .interpretationError message\n  | .exceptional state => .exceptional state',
         '| .interpretationError message => if message.isEmpty then .revert else .revert\n  | .exceptional state => .exceptional state',bind_probe),
        ('expression-helper-refusal-as-revert',
         '| .interpretationError message => .interpretationError message\n  | .exceptional final => .exceptional final',
         '| .interpretationError message => if message.isEmpty then .revert else .revert\n  | .exceptional final => .exceptional final',error_probe),
        ('expression-helper-exception-as-revert','| .exceptional final => .exceptional final',
         '| .exceptional final => if final.bindings.isEmpty then .revert else .revert',exception_probe),
        ('expression-helper-discards-world',
         '.value value { final with bindings := caller.bindings, observedReturnWords := caller.observedReturnWords }',
         '.value value { (if final.bindings.isEmpty then caller else caller) with bindings := caller.bindings, observedReturnWords := caller.observedReturnWords }',return_probe),
        ('expression-helper-leaks-locals',
         '.value value { final with bindings := caller.bindings, observedReturnWords := caller.observedReturnWords }',
         '.value value { final with bindings := if caller.bindings.isEmpty then final.bindings else final.bindings, observedReturnWords := caller.observedReturnWords }',return_probe),
        ('expression-list-discards-argument-state','evalList eval next rest',
         'evalList eval (if next.bindings.isEmpty then state else state) rest',list_probe),
        ('expression-assignment-refusal-as-revert',
         '| .interpretationError message => .interpretationError message\n  | .exceptional state => .exceptional state\n\n',
         '| .interpretationError message => if message.isEmpty then .revert else .revert\n  | .exceptional state => .exceptional state\n\n',assign_probe),
    ]
    marker_probe=probe('ofHelperBody { caller with observedReturnWords := some [55] } (.return 7 { caller with observedReturnWords := some [3, 7] })')
    mutants.append(('expression-helper-leaks-return-marker',
        '.value value { final with bindings := caller.bindings, observedReturnWords := caller.observedReturnWords }',
        '.value value { final with bindings := caller.bindings, observedReturnWords := final.observedReturnWords }',
        marker_probe))
    halt_probe=probe('ofHelperBody caller (.stop caller)')
    halt_bind_probe=probe('Result.bind (.halt caller : Result Nat) (fun _ state => .value 99 state)')
    mutants.extend([
        ('expression-helper-stop-as-refusal', '| none => .halt { final with bindings := caller.bindings }',
         '| none => .interpretationError (if caller.bindings.isEmpty then "STOP refused" else "STOP refused")', halt_probe),
        ('expression-bind-halt-as-revert', '| .halt state => .halt state',
         '| .halt state => if state.bindings.isEmpty then .revert else .revert', halt_bind_probe),
    ])
    byte_literal='([0, 1, 255, 0, 7] : List UInt8)'
    byte_assign=prefix+'''def minimal : IO Unit := do
  match assign "ignored" (.revertWithData [0, 1, 255, 0, 7]) with
  | .revertWithData data => IO.println s!"BYTES:{data}"
  | _ => IO.println "OTHER"
'''+suffix
    mutants.extend([
        ('expression-bind-erases-revert-bytes', '| .revertWithData data => .revertWithData data',
         '| .revertWithData data => .revertWithData (if data.isEmpty then [] else [])',
         probe('Result.bind (.revertWithData '+byte_literal+' : Result Nat) (fun _ state => .value 99 state)')),
        ('expression-helper-erases-revert-bytes', '| .revertWithData data => .revertWithData data',
         '| .revertWithData data => .revertWithData (if data.isEmpty then [] else [])',
         probe('ofHelperBody caller (.revertWithData '+byte_literal+')')),
        ('expression-assignment-erases-revert-bytes', '| .revertWithData data => .revertWithData data',
         '| .revertWithData data => .revertWithData (if data.isEmpty then [] else [])', byte_assign),
    ])
    files=[source,fixture_path,Path(__file__).resolve(),root/'.lake/build/lib/lean/Compiler/Proofs/IRGeneration/SourceExpressionOutcome.olean']
    identity={str(p.relative_to(root)):hashlib.sha256(p.read_bytes()).hexdigest() for p in files}
    def unchanged(): return identity=={str(p.relative_to(root)):hashlib.sha256(p.read_bytes()).hexdigest() for p in files}
    def run(name,implementation,driver):
        assert unchanged()
        path=job/(name+'.lean');path.write_text(implementation+driver)
        output=command(['lake','env','lean','--run',str(path)],cwd=root,timeout=180,log=job/(name+'.log'))
        assert unchanged()
        return output.splitlines()
    assert run('positive',definitions,fixture)==['typed helper expression outcome primitives passed','PASS']
    results=[]
    for name,before,after,witness in mutants:
        # Restrict projection mutation to the named primitive, never multiple rules.
        if name.endswith('erases-revert-bytes'):
            start,end={
                'expression-bind-erases-revert-bytes':('def Result.bind','/-- A helper'),
                'expression-helper-erases-revert-bytes':('def ofHelperBody','/-- Execute the helper'),
                'expression-assignment-erases-revert-bytes':('def assign','\nend Compiler'),
            }[name]
            left,right=definitions.split(start,1);section,tail=right.split(end,1)
            assert section.count(before)==1
            mutated=left+start+section.replace(before,after)+end+tail
        elif name=='expression-bind-refusal-as-revert':
            left,right=definitions.split('/-- A helper',1);assert left.count(before)==1
            mutated=left.replace(before,after)+'/-- A helper'+right
        elif name=='expression-assignment-refusal-as-revert':
            left,right=definitions.split('def assign',1);assert right.count(before)==1
            mutated=left+'def assign'+right.replace(before,after)
        else:
            assert definitions.count(before)==1,(name,definitions.count(before))
            mutated=definitions.replace(before,after)
        smoke=run(name,mutated,fixture)
        assert len(smoke)==1 and smoke[0].startswith('FAIL:'),(name,smoke)
        expected=run(name+'-control',definitions,witness)
        actual=run(name+'-witness',mutated,witness)
        replay=run(name+'-replay',mutated,witness)
        assert len(expected)==len(actual)==1 and expected!=actual and replay==actual
        results.append({'name':name,'expected':expected,'actual':actual,'replay':replay,'smoke':smoke})
        print(name,'detected and independently replayed',flush=True)
    (job/'success.json').write_text(json.dumps({'exit':0,'identity':identity,'sources_unchanged':unchanged(),'mutants':results,
        'scope':'Typed expression outcome primitives only, not recursive evaluator migration/whole-function A/B/C'},indent=2))

if __name__=='__main__': main()
