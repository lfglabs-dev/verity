"""Executable mutations of recursive typed expression/statement transport."""
import argparse
import hashlib
import json
import os
from pathlib import Path
from .engine import command


def main():
    root=Path(__file__).resolve().parents[2]
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output',type=Path,required=True)
    parser.add_argument('--only', action='append', default=[], help='Target named mutants; default runs every rule')
    args=parser.parse_args()
    job=args.output.resolve();job.mkdir(parents=True,exist_ok=False)
    command(['lake','build','Contracts.SolidityImportSmoke.SourceStatementEvaluationChecks'],cwd=root,timeout=1800,log=job/'build.log')
    expr=root/'Compiler/Proofs/IRGeneration/SourceExpressionEvaluation.lean'
    stmt=root/'Compiler/Proofs/IRGeneration/SourceStatementEvaluation.lean'
    fixture=root/'Contracts/SolidityImportSmoke/SourceStatementEvaluationChecks.lean'
    e=expr.read_text().split('theorem eval_fuel_zero',1)[0]+'\nend Compiler.Proofs.IRGeneration.SourceExpressionEvaluation\n'
    s=stmt.read_text().split('theorem consume_refusal',1)[0]+'\nend Compiler.Proofs.IRGeneration.SourceStatementEvaluation\n'
    copy=root/'Verity/Core/Model/ReturndataCopy.lean'
    source=root/'Compiler/Proofs/IRGeneration/SourceSemantics.lean'
    copy_defs='\n'.join(line for line in copy.read_text().split('theorem run_in_bounds',1)[0].splitlines() if not line.startswith('import '))+'\n'
    copy_defs=copy_defs.replace('namespace Verity.Core.Model.ReturndataCopy',
                                'namespace Verity.Core.Model.ReturndataCopyMutation')
    copy_defs+='\nend Verity.Core.Model.ReturndataCopyMutation\n'
    source_copy=source.read_text().split('def execReturndataCopy',1)[1].split('def execForEachLoop',1)[0]
    source_copy='namespace Compiler.Proofs.IRGeneration.SourceCopyMutation\nopen SourceSemantics\ndef execReturndataCopy'+source_copy+'\nend Compiler.Proofs.IRGeneration.SourceCopyMutation\n'
    source_copy=source_copy.replace('Verity.Core.Model.ReturndataCopy.run','Verity.Core.Model.ReturndataCopyMutation.run')
    definitions=(e+copy_defs+source_copy+s.split('\n',1)[1]).replace('SourceExpressionEvaluation','ExpressionEvaluationMutation').replace('SourceStatementEvaluation','StatementEvaluationMutation')
    definitions=definitions.replace('execReturndataCopy next dst src extent',
                                    'SourceCopyMutation.execReturndataCopy next dst src extent')
    driver='\n'.join(line for line in fixture.read_text().splitlines() if not line.startswith('import ')).replace('SourceExpressionEvaluation','ExpressionEvaluationMutation').replace('SourceStatementEvaluation','StatementEvaluationMutation')
    prefix=driver.split('def runChecks',1)[0]
    end='\nend SolidityImportSmoke.StatementEvaluationMutationChecks\ndef main : IO Unit := SolidityImportSmoke.StatementEvaluationMutationChecks.minimal\n'
    smoke=driver.replace('def main : IO Unit := SolidityImportSmoke.StatementEvaluationMutationChecks.runChecks',
        'def main : IO Unit := do\n  try\n    SolidityImportSmoke.StatementEvaluationMutationChecks.runChecks\n    IO.println "PASS"\n  catch error => IO.println s!"FAIL:{error}"')
    def witness(statement):
        return prefix+'def minimal : IO Unit := do\n  match StatementEvaluationMutation.execStmt model [] 64 caller '+statement+''' with
  | .interpretationError message => IO.println s!"ERROR:{message}"
  | .continue next => IO.println s!"CONTINUE:{lookupValue next.bindings "answer"}"
  | .stop _ => IO.println "STOP"
  | .revert => IO.println "REVERT"
  | .revertWithData data => IO.println s!"REVERTBYTES:{data}"
  | _ => IO.println "OTHER"
'''+end
    refusal=witness('(.require (.internalCall "refused" []) "message")')
    poststate=witness('(.letVar "answer" (.add (.internalCall "value" []) (.mload (.literal 96))))')
    loop=witness('(.forEach "i" (.literal 1) [.letVar "answer" (.internalCall "refused" [])])')
    unsupported=witness('(.returnArray "not-supported")')
    def observation(statement, state="caller", model="model"):
        return prefix+'def minimal : IO Unit := do\n  let initial := '+state+'\n  match StatementEvaluationMutation.execStmt '+model+' [] 64 initial '+statement+""" with
  | .continue next => IO.println s!"CONTINUE:{(next.immutable "created").val}:{(next.world.byteMemory.readByte 7).val}:{next.world.events.length}:{lookupValue next.bindings "first"}:{lookupValue next.bindings "outer"}:{(next.world.memory 0).val}:{next.observedReturnWords}:{next.externalCallIndex}:{(next.world.readSlot 0).val}:{next.world.returndata}"
  | .stop next => IO.println s!"STOP:{next.observedReturnWords}:{next.externalCallIndex}:{(next.world.readSlot 0).val}:{next.world.returndata}"
  | .exceptional next => IO.println s!"EXCEPTION:{next.executionContext.map (fun ctx => ctx.opcode.gas)}"
  | .interpretationError message => IO.println s!"ERROR:{message}"
  | .revert => IO.println "REVERT"
  | .revertWithData data => IO.println s!"REVERTBYTES:{data}"
  | _ => IO.println "OTHER"
"""+end
    returns=observation('(.returnValues [.literal 3, .literal 7])')
    immutable=observation('(.setImmutable "created" (.literal 7))')
    calldata=observation('(.calldatacopy (.literal 7) (.literal 1) (.literal 1))',
        '{ caller with selector := 0x12345678 }')
    returndata=observation('(.returndataCopy (.literal 7) (.literal 29) (.literal 1))',
        '{ caller with world := { caller.world with returndata := [0xabcdef] } }')
    bounds=observation('(.returndataCopy (.literal 0) (.literal 0) (.literal 1))',
        '{ caller with executionContext := some { opcode := { gas := 100, depth := 2, isStatic := false }, warm := fun _ => false } }')
    mutants=[
        ('typed-expression-add-discards-left-state',
         'eval runBody spec fields fuel aState b',
         'eval runBody spec fields fuel (if aState.bindings.isEmpty then state else state) b',poststate,'expression-add'),
        ('typed-statement-consumer-refusal-as-revert',
         '| .interpretationError message => .interpretationError message',
         '| .interpretationError message => if message.isEmpty then .revert else .revert',refusal,'consume'),
        ('typed-loop-discards-refusal',
         '| .interpretationError message => .interpretationError message',
         '| .interpretationError message => if message.isEmpty then .continue state else .continue state',loop,'loop'),
        ('typed-unsupported-statement-as-stop',
         '| _ => .interpretationError "unsupported typed source statement construct"',
         '| _ => .stop state',unsupported,'all'),
    ]
    mutants.extend([
        ('typed-return-values-reversed', 'some (values.map wordNormalize)',
         'some (values.reverse.map wordNormalize)', returns, 'all'),
        ('typed-immutable-value-discarded', 'Verity.Core.Uint256.ofNat value else next.immutable query',
         'Verity.Core.Uint256.ofNat (value + 1) else next.immutable query', immutable, 'all'),
        ('typed-calldata-source-offset-shifted', 'copyPhysicalCalldata next.selector dst src extent',
         'copyPhysicalCalldata next.selector dst (src + 1) extent', calldata, 'all'),
        ('typed-returndata-source-offset-shifted', 'copyPhysicalReturndata destination source size',
         'copyPhysicalReturndata destination (source + 1) size', returndata, 'all'),
        ('typed-returndata-exception-keeps-gas', 'actual.opcode with gas := 0',
         'actual.opcode with gas := actual.opcode.gas', bounds, 'all'),
    ])
    event=observation('(.emit "Value" [.literal 7])', model=
        '({ model with events := [{ name := "Value", params := [{ name := "value", ty := .uint256, kind := .unindexed }] }] })')
    mutants.append(('typed-emit-drops-event', 'events := next.world.events ++ [event]',
        'events := if event.name == event.name then next.world.events else next.world.events', event, 'all'))
    pair=observation('(.internalCallAssign ["first", "second"] "pair" [])', model=
        '({ model with functions := model.functions ++ [{ name := "pair", params := [], returnType := none, returns := [.uint256, .uint256], isInternal := true, body := [.returnValues [.literal 3, .literal 7]] }] })')
    mutants.extend([
        ('typed-assigned-helper-reverses-values', 'bindValues caller.bindings names values',
         'bindValues caller.bindings names values.reverse', pair, 'all'),
        ('typed-assigned-helper-drops-caller-locals', 'bindValues caller.bindings names values',
         'bindValues final.bindings names values', pair, 'all'),
    ])
    internal_return=observation('(.letVar "first" (.internalCall "value" []))',
        state='{ caller with world := caller.world.writePhysicalMemoryValue 0 19 }')
    mutants.append(('typed-internal-return-writes-external-memory',
        'if internalFrame then .return resolved next',
        'if internalFrame && false then .return resolved next', internal_return, 'all'))
    discarded_pair=observation('(.internalCall "pair" [])',
        state='{ caller with observedReturnWords := some [55] }', model=
        '({ model with functions := model.functions ++ [{ name := "pair", params := [], returnType := none, returns := [.uint256, .uint256], isInternal := true, body := [.returnValues [.literal 3, .literal 7]] }] })')
    mutants.append(('typed-discarded-helper-leaks-return-marker',
        '.continue { final with bindings := caller.bindings, observedReturnWords := caller.observedReturnWords }',
        '.continue { final with bindings := caller.bindings, observedReturnWords := final.observedReturnWords }',
        discarded_pair, 'restore-marker'))
    halted_model='({ model with functions := model.functions ++ [{ name := "stopped", params := [], returnType := some .uint256, isInternal := true, body := [.stop] }] })'
    halted_expr=observation('(.require (.internalCall "stopped" []) "unreachable")', model=halted_model)
    halted_stmt=observation('(.internalCall "stopped" [])', model=halted_model)
    mutants.extend([
        ('typed-expression-halt-as-revert', '| .halt state => .stop state',
         '| .halt state => if state.bindings.isEmpty then .revert else .revert', halted_expr, 'all'),
        ('typed-discarded-stop-as-continue', '| none => .stop { final with bindings := caller.bindings }',
         '| none => .continue { final with bindings := caller.bindings }', halted_stmt, 'restore-stop'),
    ])
    panic_model='({ model with functions := model.functions ++ [{ name := "panicked", params := [], returnType := some .uint256, isInternal := true, body := [.panic .arithmeticOverflow] }] })'
    error_model='({ model with errors := [{ name := "Denied", params := [.uint256, .address] }] })'
    byte_fault='| .revertWithData data => .revertWithData (if data.isEmpty then [] else [])'
    mutants.extend([
        ('typed-consumer-erases-revert-bytes', '| .revertWithData data => .revertWithData data', byte_fault,
         observation('(.require (.internalCall "panicked" []) "unreachable")',model=panic_model), 'consume'),
        ('typed-discarded-helper-erases-revert-bytes', '| .revertWithData data => .revertWithData data', byte_fault,
         observation('(.internalCall "panicked" [])',model=panic_model), 'restore-stop'),
        ('typed-assigned-helper-erases-revert-bytes', '| .revertWithData data => .revertWithData data', byte_fault,
         observation('(.internalCallAssign ["first"] "panicked" [])',model=panic_model), 'assigned-bytes'),
        ('typed-custom-error-erases-revert-bytes', '| some bytes => .revertWithData bytes',
         '| some bytes => .revertWithData (if bytes.isEmpty then [] else [])',
         observation('(.revertError "Denied" [.literal 7, .literal 9])',model=error_model), 'custom-error'),
        ('typed-panic-corrupts-code', '.panic code => .revertWithData (Denote.panicBytes code.toNat)',
         '.panic code => .revertWithData (Denote.panicBytes (code.toNat + 1))',
         observation('(.panic .arithmeticOverflow)'), 'all'),
        ('typed-require-error-evaluates-success-arguments', 'if resolved != 0 then .continue next',
         'if resolved != 0 then customError spec name []',
         observation('(.requireError (.literal 1) "missing" [.internalCall "refused" []])'), 'all'),
    ])
    for name, call, probe, state in [
        ('typed-external-bind-discards-argument-state',
         '(.externalCallBind names externalName (values.map Expr.literal))',
         '(.externalCallBind ["last"] "oracle" [.internalCall "receipt" []])', 'successfulSchedule'),
        ('typed-try-external-discards-argument-state',
         '(.tryExternalCallBind successName names externalName (values.map Expr.literal))',
         '(.tryExternalCallBind "ok" ["reason"] "oracle" [.internalCall "receipt" []])', 'scheduled'),
        ('typed-ecm-discards-argument-state',
         '(.ecm mod (values.map Expr.literal))',
         '(.ecm externalModule [.internalCall "receipt" []])', 'successfulSchedule'),
    ]:
        before = 'SourceSemantics.execStmtWithEvents fields spec.events next\n            ' + call
        after = 'SourceSemantics.execStmtWithEvents fields spec.events (if next.externalCallIndex == state.externalCallIndex then state else state)\n            ' + call
        mutants.append((name, before, after,
                        observation(probe, state=state, model='externalModel'), 'all'))
    chain_probe = prefix + 'def minimal : IO Unit := do\n' + """  let chained := { model with fields := [{ name := "chain", ty := .mappingTyped (.simple .uint256), slot := some 6 }] }
  let slot := SourceSemantics.wordNormalize (SourceSemantics.mappingSlotChain 6 [7, 3])
  match StatementEvaluationMutation.execStmt chained chained.fields 64 caller
      (.setMappingChain "chain" [.internalCall "value" [], .literal 3] (.mload (.literal 96))) with
  | .continue next => IO.println s!"CONTINUE:{(next.world.readSlot slot).val}:{(next.world.memory 96).val}"
  | .interpretationError message => IO.println s!"ERROR:{message}"
  | _ => IO.println "OTHER"
""" + end
    mutants.extend([
        ('typed-mapping-chain-discards-key-state', 'spec fields fuel keyState value',
         'spec fields fuel (if keyState.bindings.isEmpty then state else state) value', chain_probe, 'all'),
        ('typed-mapping-chain-reverses-keys', '(resolvedKeys.map Expr.literal)',
         '(resolvedKeys.reverse.map Expr.literal)', chain_probe, 'all'),
    ])
    if args.only:
        assert set(args.only) <= {row[0] for row in mutants}, args.only
        mutants=[row for row in mutants if row[0] in set(args.only)]
    files=[expr,stmt,fixture,copy,source,Path(__file__).resolve()]
    identity={str(p.relative_to(root)):hashlib.sha256(p.read_bytes()).hexdigest() for p in files}
    def unchanged(): return identity=={str(p.relative_to(root)):hashlib.sha256(p.read_bytes()).hexdigest() for p in files}
    def run(name,defs,test):
        assert unchanged();path=job/(name+'.lean');path.write_text(defs+test)
        lean=str(Path(os.environ['LEAN_SYSROOT'])/'bin/lean') if os.environ.get('LAKE_OVERRIDE_LEAN')=='true' else 'lean'
        libraries = [root / '.lake/packages/evmyul/.lake/build/lib/libleanffi.so',
                     root / '.lake/packages/evmyul/.lake/build/lib/lean/evmyul_EvmYul_FFI_ffi.so']
        out=command(['lake','env',lean,*['--load-dynlib='+str(p) for p in libraries],'--run',str(path)],cwd=root,timeout=180,log=job/(name+'.log'))
        assert unchanged();return out.splitlines()
    assert run('positive',definitions,smoke)==['typed statements and recursive nested helper refusals passed','PASS']
    rows=[]
    for name,before,after,probe,scope in mutants:
        if scope=='expression-add':
            left,right=definitions.split('      | .add a b =>',1);section,tail=right.split('      | .sub a b =>',1)
            assert section.count(before)==1
            mutated=left+'      | .add a b =>'+section.replace(before,after)+'      | .sub a b =>'+tail
        elif scope=='consume':
            left,right=definitions.split('def consume',1);section,tail=right.split('def restoreCaller',1)
            assert section.count(before)==1
            mutated=left+'def consume'+section.replace(before,after)+'def restoreCaller'+tail
        elif scope in ('assigned-bytes','custom-error'):
            start,end={'assigned-bytes':('def assignHelperResult','/-- Resolved scalar errors'),
                       'custom-error':('def customError','mutual\ndef execStmtFrame')}[scope]
            left,right=definitions.split(start,1);section,tail=right.split(end,1)
            assert section.count(before)==1
            mutated=left+start+section.replace(before,after)+end+tail
        elif scope=='restore-stop':
            left,right=definitions.split('def restoreCaller',1)
            section,tail=right.split('/-- Assigned helper returns',1)
            assert section.count(before)==1
            mutated=left+'def restoreCaller'+section.replace(before,after)+'/-- Assigned helper returns'+tail
        elif scope=='restore-marker':
            left,right=definitions.split('def restoreCaller',1)
            section,tail=right.split('/-- Assigned helper returns',1)
            prefix,stop=section.split('  | .stop final =>',1)
            assert stop.count(before)==1
            mutated=left+'def restoreCaller'+prefix+'  | .stop final =>'+stop.replace(before,after)+'/-- Assigned helper returns'+tail
        elif scope=='loop':
            left,section=definitions.split('def execLoop',1);assert section.count(before)==1
            mutated=left+'def execLoop'+section.replace(before,after)
        else:
            assert definitions.count(before)==1;mutated=definitions.replace(before,after)
        failed=run(name,mutated,smoke);assert len(failed)==1 and failed[0].startswith('FAIL:'),(name,failed)
        baseline=run(name+'-baseline',definitions,probe);actual=run(name+'-witness',mutated,probe);replay=run(name+'-replay',mutated,probe)
        assert len(baseline)==len(actual)==1 and baseline!=actual and replay==actual
        rows.append({'name':name,'baseline':baseline,'actual':actual,'replay':replay,'smoke':failed})
        print(name,'detected and independently replayed',flush=True)
    (job/'success.json').write_text(json.dumps({'exit':0,'sources_unchanged':unchanged(),'identity':identity,'mutants':rows,
        'scope':f'{len(rows)} selected typed transport/copy/return/event/helper/frame/STOP/revert/external/mapping-chain controls; remaining lowering rules/canonical bridge still need coverage'},indent=2))

if __name__=='__main__':main()
