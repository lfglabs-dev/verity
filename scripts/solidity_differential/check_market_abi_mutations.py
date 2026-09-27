"""Runtime mutations of full Market decoding and struct-array member reads."""
import json
import os
from pathlib import Path
import subprocess
import sys
from .engine import HarnessError, command, write_json
from .mutations import snapshot

MUTANTS = {'import-market-root-offset': ('Compiler/SolidityImport/AbiLowering.lean',
                               ', guard (.le rawOffset (.literal (2^64-1)))',
                               ', guard (.literal 1)'),
 'import-market-root-size': ('Compiler/SolidityImport/AbiLowering.lean',
                             ', guard (.logicalNot (.slt (.sub .calldatasize (.localVar binding)) (.literal '
                             '(32*tupleHeadWords))))',
                             ', guard (.literal 1)'),
 'import-market-calldata-array-size': ('Compiler/SolidityImport/AbiLowering.lean',
                                       '(.sub .calldatasize (.mul (.literal (32*elementWords)) (.localVar '
                                       'lengthBinding))))) ]',
                                       '(.sub .calldatasize (.mul (.literal 0) (.localVar lengthBinding))))) '
                                       ']'),
 'import-market-memory-panic': ('Compiler/SolidityImport/AbiLowering.lean',
                                'Stmt.ite condition [] [.panicCode (.literal 0x41)]\n  [ guard (.le relative',
                                'Stmt.ite condition [] [.panicCode (.literal 0x32)]\n'
                                '  [ guard (.le relative'),
 'import-market-struct-source-stride': ('Compiler/SolidityImport/AbiLowering.lean',
                                        '[ .letVar source (.add data (.mul (.localVar index) (.literal '
                                        '(32*fields.length))))',
                                        '[ .letVar source (.add data (.mul (.localVar index) (.literal '
                                        '32)))'),
 'import-market-struct-pointer-stride': ('Compiler/SolidityImport/AbiLowering.lean',
                                         '(.mul (.localVar index) (.literal 32))) (.localVar element)',
                                         '(.mul (.localVar index) (.literal 64))) (.localVar element)'),
 'import-market-struct-validation': ('Compiler/SolidityImport/AbiLowering.lean',
                                     'let checks := if bound = 2^256 then [] else [guard (.lt value '
                                     '(.literal bound))]\n'
                                     '    checks ++',
                                     'let checks := if bound = 2^256 then [] else [guard (.literal 1)]\n'
                                     '    checks ++'),
 'import-market-calldata-element-stride': ('Compiler/SolidityImport/Import.lean',
                                           '(.add (.localVar data) (.mul key.expr (.literal '
                                           '(32*fields.length)))) pre)',
                                           '(.add (.localVar data) (.mul key.expr (.literal 32))) pre)'),
 'import-market-memory-element-stride': ('Compiler/SolidityImport/Import.lean',
                                         '(.mload (.add (.add array (.literal 32)) (.mul key.expr (.literal '
                                         '32)))) pre)',
                                         '(.mload (.add (.add array (.literal 32)) (.mul key.expr (.literal '
                                         '64)))) pre)'),
 'import-market-member-validation': ('Compiler/SolidityImport/Import.lean',
                                     'let pre := if mem.calldataLocation && bound < 2^256 then\n'
                                     '              pre.push (AbiLowering.guard (.lt value (.literal '
                                     'bound))) else pre',
                                     'let pre := if mem.calldataLocation && bound < 2^256 then\n'
                                     '              pre.push (AbiLowering.guard (.literal 1)) else pre'),
 'import-market-root-scalar-validation': ('Compiler/SolidityImport/AbiRootLowering.lean',
                                          'if bound < 2^256 then body := body ++ [guard (.lt value (.literal '
                                          'bound))]',
                                          'if bound < 2^256 then body := body ++ [guard (.literal 1)]'),
 'import-market-memory-scalar-read': ('Compiler/SolidityImport/AbiRootLowering.lean',
                                      'if inMemory then ([], .mload (.add (.localVar plan.memoryPointer) '
                                      '(.literal (32*index))))',
                                      'if inMemory then ([], .mload (.add (.localVar plan.memoryPointer) '
                                      '(.literal (32*(index+1)))))'),
 'import-market-calldata-scalar-read': ('Compiler/SolidityImport/AbiRootLowering.lean',
                                        'let value := Expr.calldataload (.add (.localVar '
                                        'plan.calldataPointer) (.literal (32*index)))',
                                        'let value := Expr.calldataload (.add (.localVar '
                                        'plan.calldataPointer) (.literal (32*(index+1))))'),
 'import-market-calldata-root-validation': ('Compiler/SolidityImport/AbiRootLowering.lean',
                                            '(if bound < 2^256 then [guard (.lt value (.literal bound))] '
                                            'else [], value)',
                                            '(if bound < 2^256 then [guard (.literal 1)] else [], value)'),
 'import-market-calldata-index-bounds': ('Compiler/SolidityImport/Import.lean',
                                         'let pre := pre ++ checks.toArray ++ #[.ite (.lt key.expr '
                                         '(.localVar length))\n'
                                         '              [] [.panicCode (.literal 0x32)]]',
                                         'let pre := pre ++ checks.toArray ++ #[.ite (.literal 1)\n'
                                         '              [] [.panicCode (.literal 0x32)]]')}

def run(directory, output):
    environment = dict(os.environ)
    environment['PYTHONPATH'] = str(directory / 'scripts')
    result = subprocess.run([sys.executable, '-m', 'solidity_differential.check_market_abi',
        '--output', str(output)], cwd=directory, env=environment,
        text=True, capture_output=True, timeout=1200)
    output.with_suffix('.log').write_text(result.stdout + result.stderr)
    path = output / 'campaign.json'
    if not path.exists():
        raise HarnessError(f'ABI mutation has no runtime report: {output}; tool failure is not detection')
    return result.returncode, json.loads(path.read_text())


def mutation_campaign(output, selected=None):
    output = Path(output).resolve()
    output.mkdir(parents=True, exist_ok=True)
    reports = []
    for name in selected or MUTANTS:
        relative, before, after = MUTANTS[name]
        directory = output / name
        snapshot(directory)
        code, baseline = run(directory, directory / '.lake/baseline')
        if code or not baseline['transactions'] or baseline['divergences']:
            raise HarnessError(f'{name}: positive control failed')
        source = directory / relative
        text = source.read_text()
        if text.count(before) != 1:
            raise HarnessError(f'{name}: nonunique mutation anchor')
        source.write_text(text.replace(before, after))
        command(['lake', 'build', 'Compiler.SolidityImport.Import'], cwd=directory,
            timeout=600, log=directory / 'build.log')
        campaign = directory / '.lake/mutated'
        code, report = run(directory, campaign)
        if not code or not report['divergences']:
            raise HarnessError(f'{name}: mutation survived')
        witness = json.loads((campaign / 'witness.json').read_text())
        if not witness['deletion_minimal'] or not witness['transactions'] or not witness['signature']:
            raise HarnessError(f'{name}: missing reproduced minimal witness')
        reports.append({'mutant': name, 'status': 'detected', 'detected': True,
            'baselinePassed': True, 'witness': witness, 'campaign': str(campaign)})
        write_json(output / 'mutation-results.json', reports)
        print(f'{name}: detected and reduced', flush=True)
    return {'mutants': reports, 'divergences': []}
