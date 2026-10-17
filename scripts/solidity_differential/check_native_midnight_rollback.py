"""Compare actual solc/IdLib create-success/event/revert rollback on Foundry."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import sys
import subprocess

SCRIPT=Path(__file__).resolve()
REPO=SCRIPT.parents[2]
ROOT=REPO
HERE=REPO/'artifacts/native-midnight-source-rollback'
sys.path.insert(0,str(REPO/'scripts'))
from solidity_differential.anvil import Anvil
from solidity_differential.native_midnight_source_tools import launch, identity


def sha(path):return hashlib.sha256(path.read_bytes()).hexdigest()
def number(value):return int(value,16) if isinstance(value,str) else value


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output',required=True,type=Path)
    parser.add_argument('--foundry',required=True,type=Path)
    output,foundry,native_log,driver=launch(parser.parse_args(),'NativeMidnightRollbackChecks','runChecks',
        namespace='MidnightSourceRollback',capture='check_native_midnight_rollback_capture.py')
    manifest=json.loads((HERE/'manifest.json').read_text())
    assert all(sha(ROOT/n)==h for n,h in (manifest['inputs'] | manifest['generated']).items())
    sources=[SCRIPT,REPO/'scripts/check_native_midnight_rollback_capture.py',
        REPO/'scripts/solidity_differential/native_midnight_source_tools.py',
        REPO/'Contracts/SolidityImportSmoke/NativeMidnightRollbackChecks.lean',
        REPO/'Contracts/SolidityImportSmoke/NativeMidnightRollbackData.lean',
        native_log,driver,HERE/'manifest.json',REPO/'scripts/solidity_differential/anvil.py',
        foundry/'anvil',foundry/'cast']
    identities=identity(sources)
    cases=json.loads((HERE/'cases.json').read_text())
    error_selector=subprocess.check_output([str(foundry/'cast'),'sig','AfterDeploy(address)'],text=True).strip()
    event_topic=subprocess.check_output([str(foundry/'cast'),'keccak','Created(address)'],text=True).strip()
    native={}
    for line in native_log.read_text().splitlines():
        if line=='SOURCE_ROLLBACK_SUCCESS:6 actual pinned IdLib successful-creation then event/revert cases':continue
        match=re.fullmatch(r'ROLLBACK_OBS:'+':'.join([r'(\d+)']*10),line);assert match,line
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
            assert observed['status']=='revert' and observed['data']==error_selector+format(address,'064x') and observed['events']==[],observed
            assert len(observed['storage'])==1 and all(a==owner and int(s,16)==slot and int(v,16)==0 for a,s,v in observed['storage']),observed
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
            last=logs[-1];assert last['op']=='REVERT' and number(last['gas'])-number(last['gasCost'])==finalgas
            created='0x'+format(address,'040x')
            assert node.rpc('eth_getCode',created,'latest')=='0x'
            assert int(node.rpc('eth_getTransactionCount',created,'latest'),16)==0
            assert int(node.rpc('eth_getTransactionCount',owner,'latest'),16)==0
            assert node.rpc('eth_getStorageAt',owner,hex(7),'latest')=='0x'+format(23,'064x')
            emitted=[row for row in logs if row['op']=='LOG1' and row['depth']==1]
            assert len(emitted)==1
            event=emitted[0];topic,extent,position=map(number,event['stack'][-3:])
            assert topic==int(event_topic,16) and extent==32
            event_memory=bytes.fromhex(''.join(x.removeprefix('0x') for x in event['memory']))
            assert event_memory[position:position+extent]==address.to_bytes(32,'big')
            child_returns=[row for row in logs if row['op']=='RETURN' and row['depth']==2]
            assert len(child_returns)==1
            rows.append({'id':ident,'observation':observed,'boundaryGas':gas,'afterGas':aftergas,
                         'finalGas':finalgas,'created':created,'payload':case['payload']})
            assert node.rpc('evm_revert',snapshot) is True
    assert identities==identity(sources)
    (output/'success.json').write_text(json.dumps({'identity':identities,'cases':rows,
       'scope':'actual pinned IdLib successful native/model creation then root-revert calibration; Foundry rollback, not universal native rollback proof',
       'publicationHeadCertified':False},indent=2)+'\n')
    print('PASS:6 actual IdLib successful-create/event/revert rollback comparisons')


if __name__=='__main__':main()
