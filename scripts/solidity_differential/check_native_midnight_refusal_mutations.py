"""Execute source collision/ABI refusal mutants; compile failures never count."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess

ROOT=Path(__file__).resolve().parents[2]


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output',required=True,type=Path)
    output=parser.parse_args().output.resolve();output.mkdir(parents=True,exist_ok=False)
    fixtures={
        'collision':ROOT/'Contracts/SolidityImportSmoke/NativeMidnightCollisionChecks.lean',
        'invalid':ROOT/'Contracts/SolidityImportSmoke/NativeMidnightInvalidChecks.lean'}
    functions={'collision':'runFailures','invalid':'runInvalid'}
    success={'collision':'SOURCE_COLLISION_SUCCESS:12 actual pinned IdLib collision/revert cases\n',
             'invalid':'SOURCE_INVALID_SUCCESS:24 malformed ABI native rejections\n'}
    paths=list(fixtures.values())+[Path(__file__),
        ROOT/'Contracts/SolidityImportSmoke/NativeMidnightSourceData.lean',
        ROOT/'Contracts/SolidityImportSmoke/NativeMidnightInvalidData.lean']
    hashes={str(p.relative_to(ROOT)):hashlib.sha256(p.read_bytes()).hexdigest() for p in paths}
    lean=(str(Path(os.environ['LEAN_SYSROOT'])/'bin/lean')
          if os.environ.get('LAKE_OVERRIDE_LEAN')=='true' and os.environ.get('LEAN_SYSROOT') else 'lean')
    command=['lake','env',lean,'--load-dynlib=.lake/packages/evmyul/.lake/build/lib/libleanffi.so',
        '--load-dynlib=.lake/packages/evmyul/.lake/build/lib/lean/evmyul_EvmYul_FFI_ffi.so','--run']
    def execute(name,text):
        path=output/(name+'.lean');path.write_text(text)
        result=subprocess.run(command+[str(path)],cwd=ROOT,capture_output=True,text=True,timeout=180)
        (output/(name+'.log')).write_text(result.stdout+result.stderr)
        return result
    bodies={}
    for kind,path in fixtures.items():
        text=path.read_text()+f'\ndef main : IO Unit := MidnightSourceCaller.{functions[kind]} false\n'
        control=execute(kind+'-baseline',text)
        assert control.returncode==0 and control.stdout==success[kind] and not control.stderr,control
        bodies[kind]=text
    mutations={
        'missing-native-collision':('collision','entry.machine.accountMap.insert target collisionAccount','entry.machine.accountMap'),
        'missing-canonical-collision':('collision','creationAccounts := fun address => if address == target.val then','creationAccounts := fun address => if false then'),
        'valid-abi-in-refusal':('invalid','calldata := calldata','calldata := (let _ := calldata; (cases.head!).2.2.1)'),
    }
    rows=[]
    for name,(kind,old,new) in mutations.items():
        assert bodies[kind].count(old)==1,name
        text=bodies[kind].replace(old,new)
        failures=[]
        for suffix in ['', '-replay']:
            result=execute(name+suffix,text);log=result.stdout+result.stderr
            assert result.returncode!=0 and not re.search(r'\berror:|\bwarning:',log),log
            observed=[line for line in log.splitlines() if line.startswith(
                'uncaught exception: source collision' if kind=='collision' else 'uncaught exception: invalid ABI')]
            assert len(observed)==1,log
            failures.append(observed)
        assert failures[0]==failures[1]
        rows.append({'name':name,'detected':failures[0],'replay':failures[1],
            'sourceSha256':hashlib.sha256(text.encode()).hexdigest()})
        print('DETECTED:'+name,flush=True)
    assert hashes=={str(p.relative_to(ROOT)):hashlib.sha256(p.read_bytes()).hexdigest() for p in paths}
    (output/'success.json').write_text(json.dumps({'exit':0,'sourceHashes':hashes,'rows':rows},indent=2)+'\n')
    print('pass source refusal mutations:3 semantic detections and replays')


if __name__=='__main__':
    main()
