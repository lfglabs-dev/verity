"""Calibrate typed Source/Denote/IR-prepared memory and native CREATE2 on real EVM.

A component boundary test, not imported Solidity/compiler whole-function A/B/C.
"""
import argparse
import hashlib
import json
from pathlib import Path
from .anvil import Anvil
from .engine import command


def main():
    root = Path(__file__).resolve().parents[2]
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, required=True)
    job = parser.parse_args().output.resolve()
    job.mkdir(parents=True, exist_ok=False)
    fixture = root/'Contracts/SolidityImportSmoke/NativePreparedCreationChecks.lean'
    command(['lake', 'build', 'Contracts.SolidityImportSmoke.NativePreparedCreationChecks',
             '@evmyul/+EvmYul.FFI.ffi:dynlib'], cwd=root, timeout=1800, log=job/'build.log')
    dynlib = root/'.lake/packages/evmyul/.lake/build/lib/lean/evmyul_EvmYul_FFI_ffi.so'
    extern = root/'.lake/packages/evmyul/.lake/build/lib/libleanffi.so'
    inputs = [extern, fixture, Path(__file__).resolve(), dynlib,
              root/'Compiler/Proofs/IRGeneration/NativeCreationBoundary.lean',
              root/'Compiler/Proofs/IRGeneration/IRCreationInterpreter.lean',
              root/'Compiler/Proofs/IRGeneration/SourceStatementEvaluation.lean',
              root/'Compiler/Proofs/IRGeneration/SourceExpressionEvaluation.lean',
              root/'Compiler/Proofs/IRGeneration/SourceTypedCompatibility.lean',
              root/'Compiler/Proofs/IRGeneration/DenoteTypedCreationAgreement.lean',
              root/'Verity/Core/Model/Denote.lean',
              root/'.lake/packages/evmyul/.lake/build/lib/libleanffi.a']
    identity = {str(p.relative_to(root)): hashlib.sha256(p.read_bytes()).hexdigest() for p in inputs}
    result = command(['lake', 'env', 'lean', f'--load-dynlib={extern}', f'--load-dynlib={dynlib}', '--run', str(fixture)],
                     cwd=root, timeout=1800, log=job/'lean.log')
    rows = result.splitlines()
    assert len(rows) == 3 and rows[0].startswith('ADDRESS:') and rows[1].startswith('GAS:')
    assert rows[2] == 'actual IR memory preparation and authenticated native creation passed'
    native_address, native_gas = int(rows[0].split(':')[1]), int(rows[1].split(':')[1])
    header = bytes.fromhex('600b380380600b5f395ff3')
    code = b'\x7f'+header.ljust(32,b'\0')+bytes.fromhex('5f526007600b5f5ff55f5260205ff3')
    with Anvil(job/'node') as node:
        sender = node.rpc('eth_accounts')[0]
        target = '0x'+format(4096, '040x')
        node.rpc('anvil_setCode', target, '0x'+code.hex())
        record = node.transact({'from':sender,'to':target,'gas':hex(1021000),'data':'0x'})
        observation = node.observe(record, 'prepared-create2', [])
        assert observation['status'] == 'ok' and observation['events'] == [] and observation['storage'] == []
        evm_address = int(observation['data'],16)
        trace = node.rpc('debug_traceTransaction',record['receipt']['transactionHash'],{})
        index = next(i for i,row in enumerate(trace['structLogs']) if row['op'] == 'CREATE2')
        entry = trace['structLogs'][index]
        after = next(row for row in trace['structLogs'][index+1:] if row['depth'] == entry['depth'])
        assert after['op'] == 'PUSH0'
        evm_gas = int(after['gas'],16) if isinstance(after['gas'],str) else after['gas']
        assert native_address == evm_address != 0 and native_gas == evm_gas
        (job/'trace.json').write_text(json.dumps(trace,indent=2))
    assert identity == {str(p.relative_to(root)): hashlib.sha256(p.read_bytes()).hexdigest() for p in inputs}
    (job/'success.json').write_text(json.dumps({'exit':0,'address':evm_address,'gas':evm_gas,
        'identity':identity,'bytecode':code.hex(),'observation':observation,
        'scope':'Typed Source/Denote/IR-prepared memory/authenticated native CREATE2/real EVM boundary calibration; not imported whole-function A/B/C'},indent=2))
    print(f'IR/native/real EVM prepared CREATE2 address and gas match ({evm_gas})')

if __name__ == '__main__': main()
