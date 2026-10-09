"""Real importer acceptance/rejection controls for complete Market schemas."""
import argparse
import json
from pathlib import Path
import re
import subprocess
import tempfile
from .engine import write_json

p=argparse.ArgumentParser(description=__doc__)
p.add_argument('--output',type=Path,required=True)
out=p.parse_args().output.resolve()
out.mkdir(parents=True,exist_ok=False)
repo=Path.cwd()
interface_path='pinned-midnight/IMidnight.sol'
interface=(repo/'Contracts/SolidityImportSmoke'/interface_path).read_text()
contract='pragma solidity 0.8.34;\nimport {Market} from "pinned-midnight/IMidnight.sol";\ncontract C { function f(Market memory market) external pure returns (uint256) { return 7; } }\n'
variants=[('canonical',interface,contract,'f(Market)',None)]
for name,old,new,message in [
    ('signed-root','uint256 maturity;','int256 maturity;','unsupported scalar int256'),
    ('fixed-array','CollateralParams[] collateralParams;','CollateralParams[2] collateralParams;','fixed arrays are unsupported'),
    ('nested-array','CollateralParams[] collateralParams;','CollateralParams[][] collateralParams;','expected a flat struct array element'),
    ('signed-element','uint256 lltv;','int256 lltv;','unsupported scalar int256'),
    ('dynamic-element','uint256 lltv;','uint256[] lltv;','expected an unsigned scalar type'),
    ('bytes-element','uint256 lltv;','bytes16 lltv;','unsupported scalar bytes16')]:
    if interface.count(old) != 1:
        raise RuntimeError(f'nonunique pinned Market mutation anchor: {name}')
    variants.append((name,interface.replace(old,new),contract,'f(Market)',message))
computed=contract.replace('Market memory market','Market calldata market, uint256 i').replace('return 7;','return uint256(uint160(market.collateralParams[i + 1].token));')
variants.append(('computed-index',interface,computed,'f(Market, uint256)',None))
assign_computed=computed.replace('i + 1','i += 1')
variants.append(('assignment-index',interface,assign_computed,'f(Market, uint256)','compound assignment expressions are outside this slice'))
mixed=contract.replace('contract C','struct Tiny { uint256 value; }\ncontract C').replace('Market memory market','Market memory market, Tiny memory other')
variants.append(('mixed-structs',interface,mixed,'f(Market, Tiny)','mixed static and dynamic struct parameters'))
results=[]
project_parent=repo/'.lake/imported-market-rejections'
project_parent.mkdir(parents=True,exist_ok=True)
project_root=Path(tempfile.mkdtemp(prefix=out.name+'-',dir=project_parent))
for name,interface_text,source,signature,message in variants:
    project=project_root/name
    project.mkdir(parents=True,exist_ok=False)
    dest=project/interface_path
    dest.parent.mkdir(parents=True)
    dest.write_text(interface_text)
    (project/'Case.sol').write_text(source)
    artifact=project/'Check.olean'
    driver=project/'Check.lean'
    driver.write_text('import Compiler.SolidityImport.Import\nimport Compiler.SolidityImport.Coverage\n'
      'open Compiler.CompilationModel Compiler.CompilationModel.SolidityImport\n'
      f'solidity_import tested from {json.dumps(str(project))} entry "Case.sol"\n'
      '  using { evmVersion := "osaka", viaIR := true, optimizerRuns := some 466, bytecodeHash := "none" }\n'
      f'  contract C\n  function {signature}\n')
    if message is None:
        with driver.open('a') as out_driver:
            out_driver.write('example : (tested.model.functions.map (fun fn => fn.abiDecoding)) = [.explicitPrelude] := by decide\n')
            out_driver.write('example : tested.report.projections.isEmpty = true := by decide\n')
    proc=subprocess.run(['lake','env','lean','-j1',str(driver),'-o',str(artifact)],text=True,capture_output=True,timeout=180)
    log=proc.stdout+proc.stderr
    (out/(name+'.log')).write_text(log)
    if message is None:
        assert proc.returncode==0 and artifact.exists(),log
        # Complete ABI metadata is checked by the permanent A/B/C driver.
    else:
        assert proc.returncode!=0 and not artifact.exists(),log
        assert message in log,log
        assert re.search(r'(?:Case\.sol|pinned-midnight/IMidnight\.sol):\d+:\d+:',log),log
    results.append({'name':name,'accepted':proc.returncode==0,'expected':message or 'accepted'})
    write_json(out/'results.json',results)
    print('PASS',name,flush=True)
write_json(out/'complete.json',{'exit':0,'cases':len(results)})
