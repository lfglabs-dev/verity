"""Compare actual solc/IdLib caller bytecode and dynamic Market ABI on Foundry."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import sys

SCRIPT=Path(__file__).resolve()
REPO=SCRIPT.parents[2]
ROOT=REPO
HERE=REPO/'artifacts/native-midnight-source-caller'
sys.path.insert(0,str(REPO/'scripts'))
from solidity_differential.anvil import Anvil
from solidity_differential.native_midnight_source_tools import launch, identity


def sha(path):return hashlib.sha256(path.read_bytes()).hexdigest()
def number(value):return int(value,16) if isinstance(value,str) else value


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output',required=True,type=Path)
    parser.add_argument('--foundry',required=True,type=Path)
    output,foundry,native_log,driver=launch(parser.parse_args(),'NativeMidnightCollisionChecks','runFailures')
    manifest=json.loads((HERE/'manifest.json').read_text())
    assert all(sha(ROOT/n)==h for n,h in (manifest['inputs'] | manifest['generated']).items())
    native={}
    for line in native_log.read_text().splitlines():
        if line=='SOURCE_COLLISION_SUCCESS:12 actual pinned IdLib collision/revert cases':continue
        match=re.fullmatch(r'COLLISION_OBS:'+':'.join([r'(\d+)']*9),line);assert match,line
        count,key,kind,boundarygas,aftergas,gas,data,size,target=map(int,match.groups())
        assert (count,key,kind) not in native
        native[count,key,kind]=(boundarygas,aftergas,gas,data,size,target)
    cases=json.loads((HERE/'cases.json').read_text())
    assert set(native)=={(c['count'],c['key'],kind) for c in cases for kind in [1,2]}
    compiled=json.loads((HERE/'output.json').read_text())['contracts']['SourceCaller.sol']['SourceCaller']
    code=compiled['evm']['deployedBytecode']['object'];owner='0x'+format(8193,'040x');rows=[]
    sources=[SCRIPT, REPO/'scripts/check_native_midnight_source_capture.py',
        REPO/'scripts/solidity_differential/native_midnight_source_tools.py',
        REPO/'Contracts/SolidityImportSmoke/NativeMidnightCollisionChecks.lean',
        REPO/'Contracts/SolidityImportSmoke/NativeMidnightSourceData.lean',
        REPO/'Contracts/SolidityImportSmoke/NativeMidnightInvalidData.lean',
        native_log,driver,HERE/'manifest.json',HERE/'invalid-cases.json',
        foundry/'anvil',foundry/'cast',REPO/'scripts/solidity_differential/anvil.py']
    identities=identity(sources)
    with Anvil(output/'node') as node:
        sender=node.rpc('eth_accounts')[0]
        for case in cases:
            for kind in [1,2]:
                count,key=case['count'],case['key'];boundarygas,aftergas,gas,data,size,target=native[count,key,kind]
                snapshot=node.rpc('evm_snapshot');created='0x'+format(target,'040x')
                node.rpc('anvil_setCode',owner,'0x'+code)
                node.rpc('anvil_setStorageAt',owner,hex(7),'0x'+format(23,'064x'))
                if kind==1:node.rpc('anvil_setNonce',created,'0x1')
                else:node.rpc('anvil_setCode',created,'0x00')
                calldata=bytes.fromhex(case['calldata']);intrinsic=21000+sum(4 if b==0 else 16 for b in calldata)
                record=node.transact({'from':sender,'to':owner,'data':'0x'+calldata.hex(),'gas':hex(5000000+intrinsic)})
                ident=f'{count}:{key}:{kind}';observed=node.observe(record,ident)
                assert observed['status']=='revert' and observed['data']=='0x'+data.to_bytes(size,'big').hex() and observed['events']==[],observed
                assert len(observed['storage'])==1 and all(a==owner and int(v,16)==0 for a,s,v in observed['storage']),observed
                assert node.rpc('eth_getStorageAt',owner,hex(7),'latest')=='0x'+format(23,'064x')
                assert int(node.rpc('eth_getTransactionCount',owner,'latest'),16)==0
                assert int(node.rpc('eth_getTransactionCount',created,'latest'),16)==(1 if kind==1 else 0)
                assert node.rpc('eth_getCode',created,'latest')==('0x' if kind==1 else '0x00')
                trace=node.rpc('debug_traceTransaction',record['receipt']['transactionHash'],{'enableMemory':True})
                (output/(ident+'-trace.json')).write_text(json.dumps(trace,indent=2)+'\n');logs=trace['structLogs']
                indices=[i for i,row in enumerate(logs) if row['op']=='CREATE2'];assert len(indices)==1
                i=indices[0];entry=logs[i];after=next(row for row in logs[i+1:] if row['depth']==entry['depth'])
                assert number(entry['gas'])==boundarygas and number(after['gas'])==aftergas and number(after['stack'][-1])==0
                last=logs[-1];assert last['op']=='REVERT' and number(last['gas'])-number(last['gasCost'])==gas
                rows.append({'id':ident,'observation':observed,'boundaryGas':boundarygas,'afterGas':aftergas,'finalGas':gas,'target':created})
                assert node.rpc('evm_revert',snapshot) is True
    assert identities==identity(sources)
    (output/'success.json').write_text(json.dumps({'identity':identities,'cases':rows,
        'scope':'actual solc/IdLib collision native/model and real EVM rollback calibration; not full importer equivalence',
        'publicationHeadCertified':False},indent=2)+'\n')
    print('PASS:12 actual IdLib collision/custom-revert/Foundry-rollback comparisons')


if __name__=='__main__':main()
