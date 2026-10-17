"""Kernel-check canonical IR revert slices against real EVM byte observations.

Primitive byte-memory/opcode calibration, not importer or whole-function A/B/C.
"""
import argparse
import hashlib
import json
from pathlib import Path
import random
from .anvil import Anvil
from .engine import command


def main():
    root = Path(__file__).resolve().parents[2]
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, required=True)
    parser.add_argument('--programs', type=int, default=24)
    parser.add_argument('--seed', type=int, default=2486)
    args = parser.parse_args()
    assert args.programs >= 4
    job = args.output.resolve()
    job.mkdir(parents=True, exist_ok=False)
    rng = random.Random(args.seed)
    cases = [([(0, 0x0102030405)], 27, 5), ([(0, 0x0102030405)], 30, 5),
             ([(0, 0x0102030405)], 255, 0), ([], 3, 33)]
    for _ in range(args.programs-4):
        cases.append(([(rng.randrange(64), rng.getrandbits(256)) for _ in range(rng.randrange(1,4))],
                      rng.randrange(96), rng.randrange(65)))
    command(['lake', 'build', 'Compiler.Proofs.IRGeneration.IRRevertObservation'],
            cwd=root, timeout=1800, log=job/'build.log')
    files = [p for base in ('Compiler','Verity') for p in (root/base).rglob('*.lean')]
    files += [Path(__file__).resolve()]
    identity = {str(p.relative_to(root)):hashlib.sha256(p.read_bytes()).hexdigest() for p in files}
    generated = 'import Compiler.Proofs.IRGeneration.IRRevertObservation\nopen Compiler.Proofs.IRGeneration Compiler.Yul\n'
    rows = []
    with Anvil(job/'node') as node:
        sender = node.rpc('eth_accounts')[0]
        target = '0x'+'01'*20
        for i, (ops, offset, size) in enumerate(cases):
            code = bytearray()
            for destination, value in ops:
                code += b'\x7f'+value.to_bytes(32,'big')+b'\x7f'+destination.to_bytes(32,'big')+b'\x52'
            code += b'\x7f'+size.to_bytes(32,'big')+b'\x7f'+offset.to_bytes(32,'big')+b'\xfd'
            node.rpc('anvil_setCode', target, '0x'+code.hex())
            observation = node.observe(node.transact({'from':sender,'to':target,'data':'0x',
                                                     'gas':hex(1000000)}), 'ir-revert', [])
            assert observation['status']=='revert' and observation['events']==[] and observation['storage']==[]
            payload = list(bytes.fromhex(observation['data'][2:]))
            assert len(payload)==size
            statements = [f'.exprStmt (.call "mstore" [.lit {destination}, .lit {value}])' for destination,value in ops]
            statements.append(f'.exprStmt (.call "revert" [.lit {offset}, .lit {size}])')
            plain = '['+', '.join(statements)+']'
            variants = [plain, '.map (fun stmt => .block [stmt]) '+plain,
                        '[.if_ (.lit 1) '+plain+']']
            expected = '['+', '.join(map(str,payload))+']'
            for v, body in enumerate(variants):
                if v==1: body='('+plain+').map (fun stmt => .block [stmt])'
                generated += f'''example : (match execIRStmts 64 (IRState.initial 0) ({body}) with
  | .revert final => final.revertBytes
  | _ => none) = some ({expected} : List UInt8) := by
  try simp only [List.map_cons, List.map_nil, execIRStmts, execIRStmt, evalIRExpr]
  decide
'''
            rows.append({'operations':ops,'offset':offset,'size':size,'evm':observation,'variants':3})
    (job/'Programs.lean').write_text(generated)
    command(['lake','env','lean',str(job/'Programs.lean')],cwd=root,timeout=1800,log=job/'kernel.log')
    assert identity == {str(p.relative_to(root)):hashlib.sha256(p.read_bytes()).hexdigest() for p in files}
    (job/'success.json').write_text(json.dumps({'exit':0,'identity':identity,'sources_unchanged':True,
        'rows':rows,'seed':args.seed,'scope':'Real EVM payloads verified by Lean kernel reduction of canonical IR programs; bounded primitive calibration only, not importer/adversary/whole-function equivalence.'},indent=2))
    print(f'{len(rows)} EVM cases, {3*len(rows)} kernel-checked IR variants: exact revert bytes')


if __name__ == '__main__':
    main()
