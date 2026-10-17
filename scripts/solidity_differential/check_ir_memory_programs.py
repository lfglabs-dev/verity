"""Primitive memory calibration against real EVM, DenoteMemory and effectful IR.

This is not imported Solidity/compiler whole-function A/B/C validation.
"""
import argparse
import hashlib
import json
import os
from pathlib import Path
import random
from .anvil import Anvil
from .engine import command


def main():
    root = Path(__file__).resolve().parents[2]
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, required=True)
    parser.add_argument('--seed', type=int, default=2448)
    parser.add_argument('--programs', type=int, default=32)
    args = parser.parse_args()
    assert args.programs >= 1
    job = args.output.resolve()
    job.mkdir(parents=True, exist_ok=False)
    rng = random.Random(args.seed)
    cases = [[('mstore', 1, 0x1234), ('mstore8', 31, 511)]]
    for _ in range(args.programs - 1):
        cases.append([(rng.choice(['mstore', 'mstore8']), rng.randrange(96),
                       rng.choice([0, 1, 127, 128, 255, 256, 511, 512, (1 << 256) - 1,
                                   rng.getrandbits(256)])) for _ in range(rng.randrange(1, 9))])
    command(['lake', 'build', 'Compiler.Proofs.IRGeneration.IRCreationInterpreter',
             'Verity.Core.Model.DenoteMemory'], cwd=root, timeout=1800, log=job/'build.log')
    sources = [root/'Compiler/Proofs/IRGeneration/IRCreationInterpreter.lean',
               root/'Verity/Core/Model/DenoteMemory.lean', root/'Verity/Core/ByteMemory.lean',
               Path(__file__).resolve()]
    identity = {str(p.relative_to(root)): hashlib.sha256(p.read_bytes()).hexdigest() for p in sources}
    generated = '''import Compiler.Proofs.IRGeneration.IRCreationInterpreter
import Verity.Core.Model.DenoteMemory
open Compiler.Yul Compiler.Proofs.IRGeneration
open Compiler.Proofs.IRGeneration.IRCreationInterpreter
open Compiler.CompilationModel.DenoteMemory Verity.Core.Model

def check (id : Nat) (ops : List (Bool × Nat × Nat)) : IO Unit := do
  let mut denoted := Memory.empty
  let mut statements : List YulStmt := []
  for (word, offset, value) in ops do
    let op := if word then MemoryOp.mstore offset (valueWord (Verity.Core.Uint256.ofNat value))
      else MemoryOp.mstore8 offset ⟨value % 256, Nat.mod_lt _ (by decide)⟩
    match denoteMemoryOp op denoted with
    | .ok memory => denoted := memory
    | _ => throw (IO.userError "Denote store refused")
    statements := statements ++ [.exprStmt (.call (if word then "mstore" else "mstore8")
      [.lit offset, .lit value])]
  let initial : Runtime := { state := IRState.initial 0, creationContexts := [] }
  for variant in [statements, statements.map (fun stmt => .block [stmt]),
      [.if_ (.lit 1) statements]] do
    match execStmts 256 initial variant with
    | .value _ next =>
        unless next.state.byteMemory.size == denoted.size do
          throw (IO.userError "Denote/IR memory size divergence")
        for offset in List.range 128 do
          unless next.state.byteMemory.readByte offset == denoted.readByte offset do
            throw (IO.userError s!"Denote/IR memory byte divergence at {id}:{offset}")
    | _ => throw (IO.userError "effectful IR store program refused")
  IO.println s!"SIZE:{id}:{denoted.size}"
  for offset in List.range 128 do
    IO.println s!"BYTE:{id}:{offset}:{(denoted.readByte offset).val}"

def main : IO Unit := do
'''
    for index, ops in enumerate(cases):
        generated += '  check '+str(index)+' ['+', '.join(f'({str(name == "mstore").lower()}, {offset}, {value})' for name,offset,value in ops)+']\n'
    driver = job/'Programs.lean'
    driver.write_text(generated)
    env = dict(os.environ)
    lean = str(Path(env['LEAN_SYSROOT'])/'bin/lean') if env.get('LAKE_OVERRIDE_LEAN') == 'true' else 'lean'
    command(['lake', 'env', lean, '--run', str(driver)], cwd=root, timeout=1800, log=job/'lean.log')
    rows = (job/'lean.log').read_text().splitlines()
    bytes_by_case = {i: bytearray() for i in range(len(cases))}
    sizes = {}
    for row in rows:
        fields = row.split(':')
        if fields[0] == 'SIZE': sizes[int(fields[1])] = int(fields[2])
        else:
            assert fields[0] == 'BYTE' and int(fields[2]) == len(bytes_by_case[int(fields[1])])
            bytes_by_case[int(fields[1])].append(int(fields[3]))
    assert len(sizes) == len(cases) and all(len(value) == 128 for value in bytes_by_case.values())
    def push(value, fixed=False):
        size = 32 if fixed else max(1, (value.bit_length()+7)//8)
        return bytes([0x5f+size])+value.to_bytes(size, 'big')
    observations = []
    with Anvil(job/'node') as node:
        sender = node.rpc('eth_accounts')[0]
        target = '0x'+'01'*20
        for index, ops in enumerate(cases):
            for variant in range(3):
                code = b''
                for name, offset, value in ops:
                    code += push(value, variant == 1)+push(offset, variant == 1)
                    if variant == 2: code += push(0)+bytes([0x01])
                    code += bytes([0x52 if name == 'mstore' else 0x53])
                code += push(128)+push(0)+bytes([0xf3])
                node.rpc('anvil_setCode', target, '0x'+code.hex())
                record = node.transact({'from':sender,'to':target,'gas':hex(1000000),'data':'0x'})
                obs = node.observe(record, f'{index}-{variant}', [])
                assert obs['status'] == 'ok' and obs['events'] == [] and obs['storage'] == []
                assert obs['data'] == '0x'+bytes_by_case[index].hex(), (index,variant,obs)
                observations.append({'program':index,'variant':variant,'bytecode':code.hex(),'observation':obs})
    assert identity == {str(p.relative_to(root)): hashlib.sha256(p.read_bytes()).hexdigest() for p in sources}
    (job/'success.json').write_text(json.dumps({'exit':0,'seed':args.seed,'programs':cases,
        'ir_variants':3,'evm_transactions':len(observations),'observations':observations,
        'identity':identity,'driver_sha256':hashlib.sha256(driver.read_bytes()).hexdigest(),
        'scope':'Primitive memory calibration only; no imported whole-function/compiler A/B/C claim'},indent=2))
    print(f'{len(cases)} memory programs, three IR/EVM variants, {len(observations)} real EVM transactions passed')

if __name__ == '__main__': main()
