"""Calibrate exact whole-word RETURNDATACOPY on EVM, canonical/typed Source, Denote and effectful IR.

Primitive calibration only: no imported whole-function A/B/C or gas-equivalence claim.
Exceptions are observed directly, never coerced through Anvil.observe's revert route.
"""
import argparse
import hashlib
import json
import os
from pathlib import Path
from .anvil import Anvil
from .engine import command
from .programs import returndata_primitive_programs


def push(value, fixed=False):
    width = 32 if fixed else max(1, (value.bit_length() + 7) // 8)
    return bytes([0x5f + width]) + value.to_bytes(width, 'big')


def main():
    root = Path(__file__).resolve().parents[2]
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, required=True)
    parser.add_argument('--seed', type=int, default=211)
    parser.add_argument('--programs', type=int, default=24)
    args = parser.parse_args()
    assert args.programs >= 5
    job = args.output.resolve(); job.mkdir(parents=True, exist_ok=False)
    command(['lake', 'build', 'Compiler.Proofs.IRGeneration.IRCreationInterpreter',
             'Compiler.Proofs.IRGeneration.SourceStatementEvaluation',
             'Compiler.Proofs.IRGeneration.DenoteAgreement'],
            cwd=root, timeout=1800, log=job/'build.log')
    sources = [root/'Compiler/Proofs/IRGeneration/IRCreationInterpreter.lean',
               root/'Compiler/Proofs/IRGeneration/IRInterpreter.lean',
               root/'Compiler/Proofs/IRGeneration/SourceStatementEvaluation.lean',
               root/'Compiler/Proofs/IRGeneration/SourceExpressionEvaluation.lean',
               root/'Compiler/Proofs/IRGeneration/IRRuntimeTypes.lean',
               root/'Verity/Core/Model/PhysicalCopy.lean', root/'Verity/Core/ByteMemory.lean',
               root/'Verity/Core/Model/ReturndataCopy.lean',
               root/'Verity/Core/Model/Denote.lean',
               root/'Compiler/Proofs/IRGeneration/SourceSemantics.lean',
               root/'Compiler/Proofs/IRGeneration/DenoteAgreement.lean',
               root/'scripts/solidity_differential/programs.py',
               Path(__file__).resolve()]
    identity = {str(p.relative_to(root)): hashlib.sha256(p.read_bytes()).hexdigest() for p in sources}
    cases = returndata_primitive_programs(args.seed, args.programs)
    observations = []
    with Anvil(job/'node') as node:
        sender = node.rpc('eth_accounts')[0]
        caller = '0x'+format(4096, '040x'); callee = '0x'+format(8192, '040x')
        for index, (words, destination, source, extent) in enumerate(cases):
            callee_code = b''.join(push(word)+push(32*i)+bytes([0x52]) for i, word in enumerate(words))
            callee_code += push(32*len(words))+push(0)+bytes([0xf3])
            node.rpc('anvil_setCode', callee, '0x'+callee_code.hex())
            for variant in range(3):
                fixed = variant == 1
                emit = lambda value: push(value, fixed)
                code = emit(0xabcdef)+emit(0)+bytes([0x52])
                code += emit(0)*5+emit(8192)+emit(50000)+bytes([0xf1, 0x50])
                code += emit(extent)+emit(source)+emit(destination)
                if variant == 2: code += emit(0)+bytes([0x01])
                code += bytes([0x3e])+emit(128)+emit(0)+bytes([0xf3])
                node.rpc('anvil_setCode', caller, '0x'+code.hex())
                record = node.transact({'from':sender, 'to':caller, 'gas':hex(1000000), 'data':'0x'})
                trace = node.rpc('debug_traceTransaction', record['receipt']['transactionHash'], {})
                copies = [row for row in trace['structLogs'] if row['op'] == 'RETURNDATACOPY' and row['depth'] == 1]
                assert len(copies) == 1
                entry_gas = int(copies[0]['gas'],16) if isinstance(copies[0]['gas'],str) else copies[0]['gas']
                in_bounds = source + extent <= 32*len(words)
                assert record['receipt']['logs'] == []
                touched = [(address, slot) for address, state in record['prestate'].items()
                           for slot in state.get('storage', {})]
                assert touched == [], touched
                if in_bounds:
                    observation = node.observe(record, f'{index}-{variant}', [])
                    assert observation['status'] == 'ok' and observation['storage'] == [] and observation['events'] == []
                    data = observation['data']; kind = 'value'
                else:
                    assert record['receipt']['status'] == '0x0'
                    assert record['call'].get('error') not in (None, 'execution reverted'), record['call']
                    assert int(record['receipt']['gasUsed'],16) == 1000000
                    data = '0x'; kind = 'exceptional'
                observations.append({'program':index, 'variant':variant, 'kind':kind,
                    'data':data, 'entry_gas':entry_gas, 'caller_bytecode':code.hex(),
                    'callee_bytecode':callee_code.hex(), 'receipt':record['receipt'],
                    'call':record['call'], 'touched':touched, 'trace':trace})
    (job/'evm-observations.json').write_text(json.dumps(observations, indent=2))
    (job/'source-identities.json').write_text(json.dumps(identity, indent=2))
    generated = r"""import Compiler.Proofs.IRGeneration.IRCreationInterpreter
import Compiler.Proofs.IRGeneration.SourceStatementEvaluation
import Compiler.Proofs.IRGeneration.DenoteAgreement
open Compiler Compiler.CompilationModel Compiler.Yul Compiler.Proofs.IRGeneration
open IRCreationInterpreter SourceSemantics

def model : CompilationModel := { name := "ReturndataPrimitive", fields := [], functions := [], constructor := none }

def check (id variant : Nat) (words : List Nat) (destination source extent gas : Nat)
    (exceptional : Bool) (expected : List Nat) : IO Unit := do
  let world := { (Verity.defaultState.writePhysicalMemoryValue 0 0xabcdef) with returndata := words }
  let context : Verity.Core.Model.ExecutionContext :=
    { opcode := { gas := gas, depth := 0, isStatic := false }, warm := fun _ => false }
  let sourceState : RuntimeState :=
    { world := world, bindings := [], executionContext := some context }
  let irState :=
    { ((IRState.initial 0).writePhysicalMemoryValue 0 0xabcdef) with
      returndata := words
      executionContext := some context }
  let ir : Runtime := { state := irState, creationContexts := [] }
  let stmt : YulStmt := .exprStmt (.call "returndatacopy" [.lit destination, .lit source, .lit extent])
  let stmts := if variant = 0 then [stmt] else if variant = 1 then [.block [stmt]] else [.if_ (.lit 1) [stmt]]
  let sourceOutcome := SourceStatementEvaluation.execStmt model [] 64 sourceState
    (.returndataCopy (.literal destination) (.literal source) (.literal extent))
  let irOutcome := execStmts 128 ir stmts
  let canonicalIR := Compiler.Proofs.IRGeneration.execIRStmts 128 irState stmts
  if exceptional then
    match canonicalIR with
    | .exceptional next =>
        unless next.executionContext.map (·.opcode.gas) == some 0 &&
            next.observedRevert == none && next.byteMemory.size == irState.byteMemory.size &&
            (List.range irState.byteMemory.size).all (fun offset =>
              next.byteMemory.readByte offset == irState.byteMemory.readByte offset) &&
            next.returndata == words do
          throw (IO.userError "canonical IR exception context/frame diverged")
    | _ => throw (IO.userError "canonical IR exception became another outcome")
  else
    match canonicalIR with
    | .continue next =>
        unless (List.range 128).map (fun offset =>
            (next.byteMemory.readByte offset).val) == expected && next.returndata == words do
          throw (IO.userError "canonical IR copy bytes/frame diverged")
    | _ => throw (IO.userError "canonical IR valid copy became terminal failure")
  let copyStmt := Stmt.returndataCopy (.literal destination) (.literal source) (.literal extent)
  let denoteState : Denote.DenoteState :=
    { world := world, bindings := [], executionContext := some context }
  let canonical := [SourceSemantics.execStmt [] sourceState copyStmt,
    SourceSemantics.execStmtWithEvents [] [] sourceState copyStmt,
    SourceSemantics.execStmtWithHelpers model [] 64 sourceState copyStmt,
    DenoteAgreement.toStmtResult
      (Denote.execStmt DenoteAgreement.sourceOracle [] denoteState copyStmt)]
  for outcome in canonical do
    if exceptional then
      match outcome with
      | .exceptional next =>
          unless next.executionContext.map (·.opcode.gas) == some 0 &&
              next.world.byteMemory.size == world.byteMemory.size &&
              (List.range world.byteMemory.size).all (fun offset =>
                next.world.byteMemory.readByte offset == world.byteMemory.readByte offset) &&
              next.world.returndata == words do
            throw (IO.userError "canonical exception context/frame diverged")
      | _ => throw (IO.userError "canonical copy exception became another outcome")
    else
      match outcome with
      | .continue next =>
          unless (List.range 128).map (fun offset =>
              (next.world.byteMemory.readByte offset).val) == expected &&
              next.world.returndata == words do
            throw (IO.userError "canonical copy bytes/frame diverged")
      | _ => throw (IO.userError "canonical valid copy became terminal failure")
  if exceptional then
    match sourceOutcome, irOutcome with
    | .exceptional a, .exceptional b =>
        unless a.executionContext.map (·.opcode.gas) == some 0 &&
            b.state.executionContext.map (·.opcode.gas) == some 0 && b.state.observedRevert == none do
          throw (IO.userError "exception gas or absent revert observation diverged")
    | _, _ => throw (IO.userError "copy exception became ordinary revert or success")
  else
    match sourceOutcome, irOutcome with
    | .continue a, .value _ b =>
        let ab := (List.range 128).map (fun offset => (a.world.byteMemory.readByte offset).val)
        let bb := (List.range 128).map (fun offset => (b.state.byteMemory.readByte offset).val)
        unless ab == expected && bb == expected && a.world.byteMemory.size == b.state.byteMemory.size do
          throw (IO.userError s!"actual copy byte or size divergence at {id}:{variant}")
    | _, _ => throw (IO.userError "copy success became refusal or terminal failure")
  IO.println s!"PASS:{id}:{variant}"

def main : IO Unit := do
"""
    for row in observations:
        index = row['program']; words, dst, src, size = cases[index]
        expected = list(bytes.fromhex(row['data'][2:]))
        generated += f"  check {index} {row['variant']} {words} {dst} {src} {size} {row['entry_gas']} {str(row['kind']=='exceptional').lower()} {expected}\n"
    driver = job/'Programs.lean'; driver.write_text(generated)
    env = dict(os.environ)
    lean = str(Path(env['LEAN_SYSROOT'])/'bin/lean') if env.get('LAKE_OVERRIDE_LEAN') == 'true' else 'lean'
    result = command(['lake','env',lean,'--run',str(driver)],cwd=root,timeout=1800,log=job/'lean.log')
    assert result.splitlines() == [f"PASS:{row['program']}:{row['variant']}" for row in observations]
    assert identity == {str(p.relative_to(root)): hashlib.sha256(p.read_bytes()).hexdigest() for p in sources}
    (job/'success.json').write_text(json.dumps({'exit':0,'seed':args.seed,'cases':cases,
        'observations':observations,'identity':identity,'driver_sha256':hashlib.sha256(driver.read_bytes()).hexdigest(),
        'scope':'Whole-word returndata primitive EVM/canonical Source/Denote/canonical IR/typed Source/effectful IR calibration; not imported whole-function A/B/C'},indent=2))
    print(f'{len(cases)} returndata programs, {len(observations)} EVM transactions and canonical Source/Denote/typed Source/IR checks passed')


if __name__ == '__main__': main()
