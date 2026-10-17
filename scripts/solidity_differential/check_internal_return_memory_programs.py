"""Generated solc/typed Source/compiled Verity internal-return calibration.

Models are handwritten generated CompilationModels. This is not importer
admission or canonical Denote/whole-function compiler equivalence.
"""
import argparse
import hashlib
import json
from pathlib import Path
import random
from .anvil import Anvil
from .engine import command, solc_compile
from .programs import internal_return_memory_source


def main():
    root = Path(__file__).resolve().parents[2]
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, required=True)
    parser.add_argument('--programs', type=int, default=8)
    parser.add_argument('--seed', type=int, default=2471)
    args = parser.parse_args()
    assert args.programs >= 2
    job = args.output.resolve()
    job.mkdir(parents=True, exist_ok=False)
    rng = random.Random(args.seed)
    cases = [{'initial':19, 'result':7, 'witness':9, 'overwrite':None},
             {'initial':19, 'result':7, 'witness':9, 'overwrite':23}]
    boundaries = [0, 1, 255, 256, (1 << 256)-1]
    for _ in range(args.programs-2):
        values = [rng.choice(boundaries+[rng.getrandbits(256)]) for _ in range(4)]
        cases.append(dict(zip(('initial','result','witness','overwrite'), values)))
        if rng.randrange(2): cases[-1]['overwrite'] = None
    variants = ['baseline', 'conditional', 'loop', 'stop']
    sources = {f'Case{i}_{variant}.sol': {'content':internal_return_memory_source(spec,variant)}
               for i,spec in enumerate(cases) for variant in variants}
    settings = {'viaIR':True, 'optimizer':{'enabled':True,'runs':466}, 'evmVersion':'osaka',
                'outputSelection':{'*':{'*':['evm.deployedBytecode.object','evm.methodIdentifiers']}}}
    reference = solc_compile({'language':'Solidity','sources':sources,'settings':settings},root,job/'reference')
    selector = reference['contracts']['Case0_baseline.sol']['InternalReturnMemory']['evm']['methodIdentifiers']['probe()']
    command(['lake','build','Compiler.Proofs.IRGeneration.SourceStatementEvaluation',
             'Compiler.CompilationModel','Compiler.Codegen','Compiler.Yul.PrettyPrint'],
            cwd=root,timeout=1800,log=job/'build.log')
    template = root/'scripts/solidity_differential/internal_return_memory_driver.lean.txt'
    inputs = [template, Path(__file__).resolve(), root/'scripts/solidity_differential/programs.py',
              root/'Compiler/Proofs/IRGeneration/SourceStatementEvaluation.lean',
              root/'Compiler/Proofs/IRGeneration/SourceExpressionEvaluation.lean',
              root/'Compiler/Proofs/IRGeneration/SourceExpressionOutcome.lean',
              root/'Compiler/CompilationModel/Compile.lean']
    identity = {str(p.relative_to(root)):hashlib.sha256(p.read_bytes()).hexdigest() for p in inputs}
    driver = template.read_text()+'''def check (id initial returned witness : Nat) (overwrite : Option Nat)
    (variant : Nat) (output : String) (selector : Nat) : IO Unit := do
  if variant == 3 then checkStoppedValueRejection selector
  let model := makeModel initial returned witness overwrite variant
  let state : RuntimeState := { world := Verity.defaultState, bindings := [] }
  let fn ← match model.functions[1]? with
    | some fn => pure fn
    | none => throw (IO.userError "generated caller is missing")
  match SourceStatementEvaluation.execStmts model [] 256 state fn.body with
  | .stop next =>
      let expected := [overwrite.getD initial, witness, returned]
      unless next.observedReturnWords == (if variant == 3 then none else some expected) do
        throw (IO.userError "generated typed Source helper-return divergence")
      IO.println s!"SOURCE:{id}:{variant}:PASS"
  | _ => throw (IO.userError "generated typed Source helper-return refused")
  let compiled ← IO.ofExcept (Compiler.CompilationModel.compile model [selector] .osaka)
  IO.FS.writeFile output (Compiler.Yul.render (Compiler.emitYul compiled))
def main : IO Unit := do
'''
    for i,spec in enumerate(cases):
        for v in range(4):
            overwrite = 'none' if spec['overwrite'] is None else f"(some {spec['overwrite']})"
            output = str(job/f'model-{i}-{v}.yul')
            driver += f"  check {i} {spec['initial']} {spec['result']} {spec['witness']} {overwrite} {v} {json.dumps(output)} {int(selector,16)}\n"
    (job/'Programs.lean').write_text(driver)
    lines = command(['lake','env','lean','--run',str(job/'Programs.lean')],cwd=root,
                    timeout=1800,log=job/'typed-source.log').splitlines()
    assert lines == [f'SOURCE:{i}:{v}:PASS' for i in range(len(cases)) for v in range(4)]
    observations = []
    with Anvil(job/'node') as node:
        sender = node.rpc('eth_accounts')[0]
        target = '0x'+'01'*20
        for i,spec in enumerate(cases):
            expected_words = [spec['initial'] if spec['overwrite'] is None else spec['overwrite'],
                              spec['witness'],spec['result']]
            expected_data = '0x'+''.join(format(word,'064x') for word in expected_words)
            for v,variant in enumerate(variants):
                artifact = reference['contracts'][f'Case{i}_{variant}.sol']['InternalReturnMemory']
                node.rpc('anvil_setCode',target,'0x'+artifact['evm']['deployedBytecode']['object'])
                a = node.observe(node.transact({'from':sender,'to':target,'data':'0x'+selector,
                                               'gas':hex(1000000)}),'internal-return-memory',[])
                assert a['status']=='ok' and a['data']==('0x' if variant == 'stop' else expected_data) and a['events']==[] and a['storage']==[]
                yul = job/f'model-{i}-{v}.yul'
                compiled = solc_compile({'language':'Yul','sources':{yul.name:{'content':yul.read_text()}},
                    'settings':{'optimizer':{'enabled':True,'runs':466},'evmVersion':'osaka',
                                'outputSelection':{'*':{'*':['evm.bytecode.object']}}}},root,job/f'compiled-{i}-{v}')
                code = compiled['contracts'][yul.name]['InternalReturnMemory']['evm']['bytecode']['object']
                deployed = node.transact({'from':sender,'data':'0x'+code,'gas':hex(2000000)})
                address = deployed['receipt']['contractAddress']
                assert address
                c = node.observe(node.transact({'from':sender,'to':address,'data':'0x'+selector,
                                               'gas':hex(1000000)}),'internal-return-memory',[])
                assert a == c, (i,v,a,c)
                observations.append({'case':i,'variant':variant,'reference':a,'compiled':c})
    assert identity == {str(p.relative_to(root)):hashlib.sha256(p.read_bytes()).hexdigest() for p in inputs}
    (job/'success.json').write_text(json.dumps({'exit':0,'identity':identity,'sources_unchanged':True,
        'cases':cases,'rows':observations,'seed':args.seed,
        'scope':'Generated handwritten-model solc/typed Source/compiled Verity calibration; canonical Denote, importer admission and whole-function proofs remain open; local memory obligation explicitly unchecked.'},indent=2))
    print(f'{len(cases)} programs, {len(observations)} variants: typed Source and compiled Verity match real solc/EVM')


if __name__ == '__main__':
    main()
