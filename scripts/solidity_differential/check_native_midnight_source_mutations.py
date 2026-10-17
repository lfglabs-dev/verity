"""Detect actual captured caller mutations with unchanged runtime assertions."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess

ROOT=Path(__file__).resolve().parents[2]
SUCCESS='SOURCE_CALLER_SUCCESS:6 actual pinned IdLib/Market ABI cases\n'


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output',required=True,type=Path)
    output=parser.parse_args().output.resolve()
    output.mkdir(parents=True,exist_ok=False)
    fixture=ROOT/'Contracts/SolidityImportSmoke/NativeMidnightSourceChecks.lean'
    data=ROOT/'Contracts/SolidityImportSmoke/NativeMidnightSourceData.lean'
    capture=ROOT/'artifacts/native-midnight-source-caller/output.json'
    paths=[fixture,data,capture,Path(__file__)]
    hashes={str(p.relative_to(ROOT)):hashlib.sha256(p.read_bytes()).hexdigest() for p in paths}
    code=bytes.fromhex(json.loads(capture.read_text())['contracts']['SourceCaller.sol']['SourceCaller']['evm']['deployedBytecode']['object'])
    pc=0;stores=[]
    while pc<len(code):
        op=code[pc]
        if op==0x55:stores.append(pc)
        pc+=1+(op-0x5f if 0x60<=op<=0x7f else 0)
    assert len(stores)==1,stores
    header=bytes.fromhex('600b380380600b5f395ff3')
    assert code.count(header)==1
    body=fixture.read_text()+'\ndef main : IO Unit := MidnightSourceCaller.runChecks false\n'
    loop='  for (count, key, calldata, payload) in cases do\n'
    assert body.count(loop)==1
    mutations={
        'omit-storage-write': loop+f'    let code : ByteArray := ⟨code.data.set! {stores[0]} 0x50⟩\n',
        'corrupt-initcode-header': loop+f'    let code : ByteArray := ⟨code.data.set! {code.index(header)} 0x61⟩\n',
        'corrupt-abi-root': loop+'    let calldata : ByteArray := ⟨calldata.data.set! 35 0⟩\n',
    }
    lean=(str(Path(os.environ['LEAN_SYSROOT'])/'bin/lean')
          if os.environ.get('LAKE_OVERRIDE_LEAN')=='true' and os.environ.get('LEAN_SYSROOT') else 'lean')
    command=['lake','env',lean,'--load-dynlib=.lake/packages/evmyul/.lake/build/lib/libleanffi.so',
             '--load-dynlib=.lake/packages/evmyul/.lake/build/lib/lean/evmyul_EvmYul_FFI_ffi.so','--run']
    def execute(name,text):
        path=output/(name+'.lean');path.write_text(text)
        run=subprocess.run(command+[str(path)],cwd=ROOT,capture_output=True,text=True,timeout=180)
        (output/(name+'.log')).write_text(run.stdout+run.stderr)
        return run
    baseline=execute('baseline',body)
    assert baseline.returncode==0 and baseline.stdout==SUCCESS and not baseline.stderr,baseline
    rows=[]
    for name,injection in mutations.items():
        text=body.replace(loop,injection)
        first=execute(name,text);replay=execute(name+'-replay',text)
        failures=[]
        for run in [first,replay]:
            log=run.stdout+run.stderr
            assert run.returncode!=0 and not re.search(r'\berror:|\bwarning:',log),log
            failure=[line for line in log.splitlines() if line.startswith('uncaught exception: source caller')]
            assert len(failure)==1,log
            failures.append(failure)
        assert failures[0]==failures[1]
        rows.append({'name':name,'detected':failures[0],'replay':failures[1],
                     'sourceSha256':hashlib.sha256(text.encode()).hexdigest()})
        print('DETECTED:'+name,flush=True)
    assert hashes=={str(p.relative_to(ROOT)):hashlib.sha256(p.read_bytes()).hexdigest() for p in paths}
    (output/'success.json').write_text(json.dumps({'exit':0,'sourceHashes':hashes,'rows':rows},indent=2)+'\n')
    print('pass captured Solidity caller mutations:3 semantic detections and replays')


if __name__=='__main__':
    main()
