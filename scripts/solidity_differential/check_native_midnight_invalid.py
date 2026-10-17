"""Compare native and Foundry refusal of malformed dynamic Market calldata."""
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
    output,foundry,native_log,driver=launch(parser.parse_args(),'NativeMidnightInvalidChecks','runInvalid')
    sources=[SCRIPT, REPO/'scripts/check_native_midnight_source_capture.py',
        REPO/'scripts/solidity_differential/native_midnight_source_tools.py',
        REPO/'Contracts/SolidityImportSmoke/NativeMidnightInvalidChecks.lean',
        REPO/'Contracts/SolidityImportSmoke/NativeMidnightSourceData.lean',
        REPO/'Contracts/SolidityImportSmoke/NativeMidnightInvalidData.lean',
        native_log,driver,HERE/'manifest.json',HERE/'invalid-cases.json',
        foundry/'anvil',foundry/'cast',REPO/'scripts/solidity_differential/anvil.py']
    identities=identity(sources)
    manifest=json.loads((HERE/'manifest.json').read_text());assert all(sha(ROOT/n)==h for n,h in (manifest['inputs'] | manifest['generated']).items())
    native={}
    for line in native_log.read_text().splitlines():
        if line=='SOURCE_INVALID_SUCCESS:24 malformed ABI native rejections':continue
        match=re.fullmatch(r'INVALID_OBS:(.+):(\d+)',line);assert match,line
        ident,gas=match.groups();assert ident not in native;native[ident]=int(gas)
    cases=json.loads((HERE/'invalid-cases.json').read_text());assert len(cases)==24 and set(native)=={c['id'] for c in cases}
    code=json.loads((HERE/'output.json').read_text())['contracts']['SourceCaller.sol']['SourceCaller']['evm']['deployedBytecode']['object']
    owner='0x'+format(8193,'040x');rows=[]
    with Anvil(output/'node') as node:
        sender=node.rpc('eth_accounts')[0]
        for case in cases:
            snapshot=node.rpc('evm_snapshot');node.rpc('anvil_setCode',owner,'0x'+code)
            node.rpc('anvil_setStorageAt',owner,hex(7),'0x'+format(23,'064x'))
            calldata=bytes.fromhex(case['calldata']);intrinsic=21000+sum(4 if b==0 else 16 for b in calldata)
            record=node.transact({'from':sender,'to':owner,'data':'0x'+calldata.hex(),'gas':hex(5000000+intrinsic)})
            observed=node.observe(record,case['id'])
            assert observed=={'id':case['id'],'status':'revert','data':'0x','touched':[],'storage':[],'events':[]},observed
            assert int(node.rpc('eth_getTransactionCount',owner,'latest'),16)==0
            assert node.rpc('eth_getStorageAt',owner,hex(7),'latest')=='0x'+format(23,'064x')
            trace=node.rpc('debug_traceTransaction',record['receipt']['transactionHash'],{'enableMemory':True})
            (output/(case['id']+'-trace.json')).write_text(json.dumps(trace,indent=2)+'\n');logs=trace['structLogs']
            assert not any(row['op'] in ('SSTORE','TSTORE','CREATE2','LOG0','LOG1','LOG2','LOG3','LOG4') for row in logs)
            last=logs[-1];assert last['op']=='REVERT' and number(last['gas'])-number(last['gasCost'])==native[case['id']]
            rows.append({'observation':observed,'finalGas':native[case['id']]})
            assert node.rpc('evm_revert',snapshot) is True
    assert identities==identity(sources)
    (output/'success.json').write_text(json.dumps({'identity':identities,'cases':rows,
        'scope':'malformed real solc caller ABI native/Foundry calibration, not importer rejection tests',
        'publicationHeadCertified':False},indent=2)+'\n')
    print('PASS:24 malformed actual Market ABI Foundry/native refusals')


if __name__=='__main__':main()
