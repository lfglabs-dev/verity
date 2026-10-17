"""Capture real pinned Midnight IdLib deployment caller; no importer admission."""
import argparse
import hashlib
import json
from pathlib import Path
import subprocess

SCRIPT = Path(__file__).resolve()
REPO = SCRIPT.parent.parent
ROOT = REPO
HERE = REPO / 'artifacts/native-midnight-source-rollback'
PINNED = REPO / 'Contracts/SolidityImportSmoke/pinned-midnight'
DATA = REPO / 'Contracts/SolidityImportSmoke/NativeMidnightRollbackData.lean'


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--check', action='store_true')
    args = parser.parse_args()
    generated = {}
    solc = REPO / '.lake/solidity-import/solc-0.8.34'
    assert sha(solc) in {'d40adc6f9fdbb22a97d32a02fa05688bf2ee7886affc48c9851b0afd4a726b39',
                         '0a2829292697dda542e4e365bb63fbd6d3ed51537140222a880ab760cffa7746'}
    files = {'SourceCaller.sol':HERE/'SourceCaller.sol',
             'src/libraries/IdLib.sol':PINNED/'libraries/IdLib.sol',
             'src/interfaces/IMidnight.sol':PINNED/'interfaces/IMidnight.sol'}
    assert sha(files['src/libraries/IdLib.sol']) == 'a4fad41d5f053b6f1873c728d6531694a1c348fc3488d1ae0c1571d1765e2dfb'
    assert sha(files['src/interfaces/IMidnight.sol']) == 'b1a0cbcd9de9ce3781bd12cdd0a8665361f988fd23d0219217ff4e7981710475'
    version = subprocess.check_output([str(solc),'--version'],text=True).strip()
    assert '0.8.34+commit.80d5c536' in version, version
    request = {'language':'Solidity','sources':{n:{'content':p.read_text()} for n,p in files.items()},
               'settings':{'evmVersion':'osaka','viaIR':True,'optimizer':{'enabled':True,'runs':466},
                           'metadata':{'bytecodeHash':'none'},
                           'outputSelection':{'*':{'*':['evm.deployedBytecode.object','evm.deployedBytecode.opcodes',
                                                         'evm.methodIdentifiers','irOptimized'],'':['ast']}}}}
    generated[HERE/'input.json'] = (json.dumps(request,indent=2)+'\n').encode()
    result = subprocess.run([str(solc),'--standard-json'],input=json.dumps(request),text=True,
                            capture_output=True,check=True,timeout=60)
    output=json.loads(result.stdout)
    generated[HERE/'output.json'] = (json.dumps(output,indent=2)+'\n').encode()
    assert not [e for e in output.get('errors',[]) if e['severity']=='error'],output.get('errors')
    compiled=output['contracts']['SourceCaller.sol']['SourceCaller']
    code=bytes.fromhex(compiled['evm']['deployedBytecode']['object'])
    selector=next(v for k,v in compiled['evm']['methodIdentifiers'].items() if k.startswith('deploy('))
    generated[HERE/'optimized.yul'] = compiled['irOptimized'].encode()
    def word(n):return n.to_bytes(32,'big')
    def lean_bytes(b):return '⟨#['+', '.join(f'0x{x:02x}' for x in b)+']⟩'
    lean='import Compiler.Proofs.IRGeneration.NativeHashedDenote\nnamespace MidnightSourceRollback\nopen EvmYul\ndef code : ByteArray := '+lean_bytes(code)+'\n'
    cases=[]
    for count in [0,1,2]:
        for key in [0,2**256-1]:
            market=b''.join(map(word,[1,8193,0x1111,256,123,77,0,0,count]))
            for i in range(count):market+=b''.join(map(word,[0x2222+i,123,456,0x3333]))
            payload=word(32)+market
            calldata=bytes.fromhex(selector)+word(96)+word(key)+word(99)+market
            cases.append({'count':count,'key':key,'calldata':calldata.hex(),'payload':payload.hex()})
    lean+='def cases : List (Nat × Nat × ByteArray × ByteArray) := [\n'+',\n'.join(
        '('+str(c['count'])+', '+str(c['key'])+', '+lean_bytes(bytes.fromhex(c['calldata']))+', '+lean_bytes(bytes.fromhex(c['payload']))+')' for c in cases)+']\nend MidnightSourceRollback\n'
    generated[DATA] = lean.encode()
    generated[HERE/'cases.json'] = (json.dumps(cases,indent=2)+'\n').encode()
    inputs = list(files.values()) + [solc, SCRIPT]
    manifest = {'scope':'actual pinned-library Solidity caller capture only; no importer admission',
        'pinnedMidnightHead':'96d31343e993329e7a593dde46516a2c0cbcd142',
        'compilerVersion':version,'codeBytes':len(code),'selector':selector,
        'inputs':{str(p.relative_to(ROOT)):sha(p) for p in inputs},
        'generated':{str(p.relative_to(ROOT)):hashlib.sha256(data).hexdigest() for p,data in generated.items()}}
    generated[HERE/'manifest.json'] = (json.dumps(manifest,indent=2)+'\n').encode()
    for path,data in generated.items():
        if args.check:
            assert path.read_bytes() == data, 'stale source capture: '+str(path.relative_to(ROOT))
        else:
            path.write_bytes(data)
    print('Verified' if args.check else 'Captured', 'actual IdLib rollback caller:',len(code),'runtime bytes,',len(cases),'dynamic Market inputs')


if __name__=='__main__':main()
