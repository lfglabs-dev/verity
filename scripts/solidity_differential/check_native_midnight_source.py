"""Compare actual solc/IdLib caller bytecode and dynamic Market ABI on Foundry."""
import argparse
import subprocess
import hashlib
import json
import os
from pathlib import Path
import re
import sys

SCRIPT = Path(__file__).resolve()
REPO = SCRIPT.parents[2]
ROOT = REPO
HERE = REPO/'artifacts/native-midnight-source-caller'
sys.path.insert(0,str(REPO/'scripts'))
from solidity_differential.anvil import Anvil


def sha(path):return hashlib.sha256(path.read_bytes()).hexdigest()
def number(value):return int(value,16) if isinstance(value,str) else value


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output',required=True,type=Path)
    parser.add_argument('--foundry',required=True,type=Path)
    args=parser.parse_args()
    output=args.output.resolve();output.mkdir(parents=True,exist_ok=False)
    foundry=args.foundry.resolve()
    assert sha(foundry/'anvil')=='9797b1e9bcdf65c9d6193470c94c2ee76e5524af2985cfb5db7fc641ba216cfa'
    assert sha(foundry/'cast')=='9db0414588508e131bdb4aa4bf46c3dd5357482a2ae81c48ffeeb6801a4daa8d'
    os.environ['PATH']=str(foundry)+':'+os.environ['PATH']
    subprocess.run([sys.executable,str(REPO/'scripts/check_native_midnight_source_capture.py'),'--check'],check=True)
    lean=str(Path(os.environ['LEAN_SYSROOT'])/'bin/lean') if os.environ.get('LAKE_OVERRIDE_LEAN')=='true' else 'lean'
    driver=output/'Native.lean'
    driver.write_text('import Contracts.SolidityImportSmoke.NativeMidnightSourceChecks\ndef main : IO Unit := MidnightSourceCaller.runChecks\n')
    native_log=output/'native.log'
    run=subprocess.run(['lake','env',lean,
        '--load-dynlib=.lake/packages/evmyul/.lake/build/lib/libleanffi.so',
        '--load-dynlib=.lake/packages/evmyul/.lake/build/lib/lean/evmyul_EvmYul_FFI_ffi.so',
        '--run',str(driver)],cwd=REPO,capture_output=True,text=True,timeout=180)
    native_log.write_text(run.stdout+run.stderr)
    assert run.returncode==0 and not run.stderr,run

    manifest=json.loads((HERE/'manifest.json').read_text())
    assert all(sha(ROOT/n)==h for n,h in (manifest['inputs'] | manifest['generated']).items())
    sources=[SCRIPT,REPO/'scripts/check_native_midnight_source_capture.py',
        REPO/'Contracts/SolidityImportSmoke/NativeMidnightSourceChecks.lean',
        REPO/'Contracts/SolidityImportSmoke/NativeMidnightSourceData.lean',
        native_log,driver,HERE/'manifest.json',REPO/'scripts/solidity_differential/anvil.py',
        foundry/'anvil',foundry/'cast']
    def identities_now():
        return {str(p.relative_to(ROOT)) if p.is_relative_to(ROOT) else str(p):sha(p) for p in sources}
    identities=identities_now()
    cases=json.loads((HERE/'cases.json').read_text())
    native={}
    for line in native_log.read_text().splitlines():
        if line=='SOURCE_CALLER_SUCCESS:6 actual pinned IdLib/Market ABI cases':continue
        match=re.fullmatch(r'SOURCE_OBS:'+':'.join([r'(\d+)']*10),line);assert match,line
        count,key,pc,gas,aftergas,finalgas,slot,address,offset,size=map(int,match.groups())
        assert (count,key) not in native
        native[count,key]=(pc,gas,aftergas,finalgas,slot,address,offset,size)
    assert set(native)=={(c['count'],c['key']) for c in cases}
    compiled=json.loads((HERE/'output.json').read_text())['contracts']['SourceCaller.sol']['SourceCaller']
    code=compiled['evm']['deployedBytecode']['object'];owner='0x'+format(8193,'040x');rows=[]
    with Anvil(output/'node') as node:
        sender=node.rpc('eth_accounts')[0]
        for case in cases:
            count,key=case['count'],case['key'];pc,gas,aftergas,finalgas,slot,address,offset,size=native[count,key]
            snapshot=node.rpc('evm_snapshot')
            node.rpc('anvil_setCode',owner,'0x'+code)
            node.rpc('anvil_setStorageAt',owner,hex(7),'0x'+format(23,'064x'))
            calldata=bytes.fromhex(case['calldata']);intrinsic=21000+sum(4 if b==0 else 16 for b in calldata)
            record=node.transact({'from':sender,'to':owner,'data':'0x'+calldata.hex(),'gas':hex(5000000+intrinsic)})
            ident=f'{count}:{key}';observed=node.observe(record,ident)
            assert observed['status']=='ok' and observed['data']=='0x'+format(address,'064x') and observed['events']==[],observed
            assert len(observed['storage'])==1 and all(a==owner and int(s,16)==slot and int(v,16)==99 for a,s,v in observed['storage']),observed
            trace=node.rpc('debug_traceTransaction',record['receipt']['transactionHash'],{'enableMemory':True})
            (output/(ident+'-trace.json')).write_text(json.dumps(trace,indent=2)+'\n');logs=trace['structLogs']
            assert number(logs[0]['gas'])==5000000
            indices=[i for i,row in enumerate(logs) if row['op']=='CREATE2'];assert len(indices)==1
            i=indices[0];entry=logs[i];after=next(row for row in logs[i+1:] if row['depth']==entry['depth'])
            assert number(entry['pc'])==pc and number(entry['gas'])==gas
            assert number(after['gas'])==aftergas and number(after['stack'][-1])==address
            memory=bytes.fromhex(''.join(x.removeprefix('0x') for x in entry['memory']))
            assert memory[offset:offset+size]==bytes.fromhex('600b380380600b5f395ff3'+case['payload'])
            assert [number(x) for x in entry['stack'][-4:]]==[0,size,offset,0]
            writes=[row for row in logs if row['depth']==1 and row['op']=='SSTORE'];assert len(writes)==1
            assert [number(x) for x in writes[0]['stack'][-2:]]==[99,slot]
            last=logs[-1];assert last['op']=='RETURN' and number(last['gas'])-number(last['gasCost'])==finalgas
            created='0x'+format(address,'040x')
            assert node.rpc('eth_getCode',created,'latest')=='0x'+case['payload']
            assert int(node.rpc('eth_getTransactionCount',created,'latest'),16)==1
            assert int(node.rpc('eth_getTransactionCount',owner,'latest'),16)==1
            rows.append({'id':ident,'observation':observed,'boundaryGas':gas,'afterGas':aftergas,
                         'finalGas':finalgas,'created':created,'payload':case['payload']})
            assert node.rpc('evm_revert',snapshot) is True
    assert identities==identities_now()
    (output/'success.json').write_text(json.dumps({'identity':identities,'cases':rows,
       'scope':'actual pinned IdLib Solidity caller EVM/native/canonical/Denote-boundary calibration; not importer admission or universal source-prefix proof',
       'publicationHeadCertified':False,'capture':manifest},indent=2)+'\n')
    print('PASS:6 actual pinned IdLib/Market ABI Foundry/native/Denote-boundary comparisons')


if __name__=='__main__':main()
