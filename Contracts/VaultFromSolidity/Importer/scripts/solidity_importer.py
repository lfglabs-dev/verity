#!/usr/bin/env python3
"""Closed Vault-feature typed-AST frontend. Emits JSON, never Lean source."""
import hashlib
import json
import pathlib
import platform
import re
import subprocess
import sys

ROOT = pathlib.Path(__file__).resolve().parents[4]
SOURCE = 'Contracts/VaultFromSolidity/Vault.sol'
PINS = {
    'Linux': '1274e5c4621ae478090c5a1f48466fd3c5f658ed9e14b15a0b213dc806215468',
    'Darwin': '8324280591ce398d7e2722846bc10ecf1779b13a328ef97b687c92cd9c70801a',
}
SETTINGS = dict(optimizer={'enabled': False}, viaIR=False, evmVersion='cancun',
                remappings=[], outputSelection={'*': {'': ['ast'], '*': ['storageLayout']}})

def digest(b):
    return hashlib.sha256(b).hexdigest()

# Closed schema for pinned solc's accepted AST. Metadata is explicitly typed,
# never a catch-all escape hatch for unknown executable children.
NODE_FIELDS = {
    'SourceUnit': 'absolutePath exportedSymbols license nodes',
    'PragmaDirective': 'literals',
    'ContractDefinition': 'abstract baseContracts canonicalName contractDependencies contractKind documentation fullyImplemented linearizedBaseContracts name nameLocation nodes scope usedErrors usedEvents storageLayout',
    'StructuredDocumentation': 'text',
    'VariableDeclaration': 'constant functionSelector mutability name nameLocation scope stateVariable storageLocation typeDescriptions typeName visibility value documentation overrides indexed',
    'ElementaryTypeName': 'name stateMutability typeDescriptions',
    'Mapping': 'keyName keyNameLocation keyType typeDescriptions valueName valueNameLocation valueType',
    'ErrorDefinition': 'errorSelector name nameLocation parameters documentation',
    'FunctionDefinition': 'body functionSelector implemented kind modifiers name nameLocation parameters returnParameters scope stateMutability virtual visibility documentation overrides baseFunctions',
    'ParameterList': 'parameters',
    'Block': 'statements documentation',
    'ExpressionStatement': 'expression',
    'Assignment': 'leftHandSide operator rightHandSide',
    'BinaryOperation': 'commonType leftExpression operator rightExpression function',
    'Identifier': 'argumentTypes name overloadedDeclarations referencedDeclaration',
    'MemberAccess': 'expression memberLocation memberName referencedDeclaration',
    'IndexAccess': 'baseExpression indexExpression',
    'Literal': 'hexValue kind subdenomination value',
    'FunctionCall': 'arguments expression kind nameLocations names tryCall',
    'VariableDeclarationStatement': 'assignments declarations initialValue',
    'IfStatement': 'condition trueBody falseBody',
    'RevertStatement': 'errorCall',
    'Return': 'expression functionReturnParameters',
}
EXPRESSION_NODES = {'Assignment', 'BinaryOperation', 'Identifier', 'MemberAccess',
                    'IndexAccess', 'Literal', 'FunctionCall'}
CHILDREN = {'nodes', 'baseContracts', 'parameters', 'returnParameters', 'body',
            'statements', 'typeName', 'keyType', 'valueType', 'value', 'modifiers',
            'overrides', 'storageLayout', 'leftHandSide', 'rightHandSide',
            'leftExpression', 'rightExpression', 'expression', 'baseExpression',
            'indexExpression', 'arguments', 'declarations', 'initialValue',
            'condition', 'trueBody', 'falseBody', 'errorCall'}
STRING_FIELDS = set('absolutePath license canonicalName contractKind name nameLocation text functionSelector mutability storageLocation visibility stateMutability keyName keyNameLocation valueName valueNameLocation errorSelector kind operator memberLocation memberName hexValue subdenomination'.split())
BOOL_FIELDS = set('abstract fullyImplemented constant stateVariable indexed implemented virtual isConstant isLValue isPure lValueRequested tryCall'.split())
INT_FIELDS = {'scope', 'referencedDeclaration', 'functionReturnParameters', 'function'}
INT_LIST_FIELDS = {'contractDependencies', 'linearizedBaseContracts', 'usedErrors', 'usedEvents', 'baseFunctions', 'overloadedDeclarations', 'assignments'}
STRING_LIST_FIELDS = {'literals', 'names', 'nameLocations'}


def validate_ast(ast, need):
    def types(value, owner):
        need(isinstance(value, dict) and set(value) <= {'typeIdentifier', 'typeString'}
             and all(isinstance(v, str) for v in value.values()), owner, 'invalid type metadata')
    def visit(n):
        need(isinstance(n, dict) and n.get('nodeType') in NODE_FIELDS, n if isinstance(n, dict) else ast, 'unsupported AST node')
        k = n['nodeType']
        if k == 'ContractDefinition':
            need(n.get('storageLayout') is None, n, 'contract layout at specifier unsupported')
        allowed = set(NODE_FIELDS[k].split()) | {'id', 'src', 'nodeType'}
        if k in EXPRESSION_NODES:
            allowed |= {'isConstant', 'isLValue', 'isPure', 'lValueRequested', 'typeDescriptions'}
        need(not (set(n) - allowed), n, 'unexpected AST fields: ' + ', '.join(sorted(set(n) - allowed)))
        need(type(n.get('id')) is int and isinstance(n.get('src'), str), n, 'missing AST identity/span')
        for key, v in n.items():
            if key in {'id', 'src', 'nodeType'}:
                continue
            if key == 'documentation':
                if isinstance(v, dict):
                    need(v.get('nodeType') == 'StructuredDocumentation', n, 'invalid documentation')
                    visit(v)
                else:
                    need(v is None or isinstance(v, str), n, 'invalid documentation')
            elif key in {'typeDescriptions', 'commonType'}:
                types(v, n)
            elif key == 'argumentTypes':
                need(isinstance(v, list), n, 'invalid argument type metadata')
                for t in v:
                    types(t, n)
            elif key == 'exportedSymbols':
                need(isinstance(v, dict) and all(isinstance(ids, list) and all(type(i) is int for i in ids) for ids in v.values()), n, 'invalid symbol metadata')
            elif key == 'value' and k == 'Literal':
                need(isinstance(v, str), n, 'invalid literal value')
            elif key in CHILDREN:
                if v is not None:
                    if isinstance(v, list):
                        for child in v:
                            if child is not None:
                                visit(child)
                    else:
                        visit(v)
            elif key in STRING_FIELDS:
                need(isinstance(v, str) or (key == 'subdenomination' and v is None), n, 'invalid string metadata: ' + key)
            elif key in BOOL_FIELDS:
                need(type(v) is bool, n, 'invalid boolean metadata: ' + key)
            elif key in INT_FIELDS:
                need(type(v) is int, n, 'invalid declaration metadata: ' + key)
            elif key in INT_LIST_FIELDS:
                need(isinstance(v, list) and all(type(i) is int or (key == 'assignments' and i is None) for i in v), n, 'invalid declaration list: ' + key)
            elif key in STRING_LIST_FIELDS:
                need(isinstance(v, list) and all(isinstance(i, str) for i in v), n, 'invalid string list: ' + key)
            else:
                need(False, n, 'unclassified AST field: ' + key)
        # Structural positions are closed as well as node field names. In
        # particular a known node kind in the wrong position is not metadata.
        lists = {'nodes', 'baseContracts', 'statements', 'modifiers', 'arguments', 'declarations'}
        if k == 'ParameterList':
            lists.add('parameters')
        nullable = {'value', 'overrides', 'storageLayout', 'falseBody'}
        required = {
            'SourceUnit': ('nodes',), 'ContractDefinition': ('nodes', 'baseContracts'),
            'FunctionDefinition': ('body', 'parameters', 'returnParameters', 'modifiers'),
            'ParameterList': ('parameters',), 'Block': ('statements',),
            'VariableDeclaration': ('typeName',), 'Mapping': ('keyType', 'valueType'),
            'ExpressionStatement': ('expression',), 'Assignment': ('leftHandSide', 'rightHandSide'),
            'BinaryOperation': ('leftExpression', 'rightExpression'),
            'MemberAccess': ('expression',), 'IndexAccess': ('baseExpression', 'indexExpression'),
            'FunctionCall': ('expression', 'arguments'),
            'VariableDeclarationStatement': ('declarations', 'initialValue'),
            'IfStatement': ('condition', 'trueBody'), 'RevertStatement': ('errorCall',),
            'Return': ('expression',), 'ErrorDefinition': ('parameters',),
        }
        need(all(key in n for key in required.get(k, ())), n, 'missing required AST children')
        for key in CHILDREN & n.keys():
            if key == 'value' and k == 'Literal':
                continue
            v = n[key]
            if key in lists:
                need(isinstance(v, list) and all(isinstance(child, dict) for child in v), n, 'invalid AST child list: ' + key)
            else:
                need(isinstance(v, dict) or (key in nullable and v is None), n, 'invalid AST child: ' + key)
        expected = {'typeName': {'ElementaryTypeName', 'Mapping'},
                    'keyType': {'ElementaryTypeName'}, 'valueType': {'ElementaryTypeName'},
                    'errorCall': {'FunctionCall'}, 'trueBody': {'Block'}}
        for key, kinds in expected.items():
            if key in n:
                need(n[key].get('nodeType') in kinds, n, 'unexpected child kind: ' + key)
        if k == 'ParameterList':
            need(all(p['nodeType'] == 'VariableDeclaration' for p in n['parameters']), n, 'invalid parameter declaration')
        if k == 'VariableDeclarationStatement':
            need(all(p['nodeType'] == 'VariableDeclaration' for p in n['declarations']), n, 'invalid local declaration')
        if k == 'VariableDeclaration':
            need(n.get('value') is None and n.get('overrides') is None, n, 'initializer/override unsupported')
        if k == 'BinaryOperation':
            need(n.get('function') is None, n, 'user-defined operator unsupported')
        if k == 'FunctionCall':
            need(n['kind'] == 'functionCall' and not n['tryCall'] and not n['names'], n, 'unsupported call surface')
        if k == 'FunctionDefinition':
            need(isinstance(n.get('body'), dict) and n['body'].get('nodeType') == 'Block', n, 'function body must be Block')
        for key in ('parameters', 'returnParameters'):
            if key in n and k != 'ParameterList':
                need(isinstance(n[key], dict) and n[key].get('nodeType') == 'ParameterList', n, key + ' must be ParameterList')
        if k == 'Block':
            need(isinstance(n.get('statements'), list), n, 'Block requires statements')
    need(isinstance(ast, dict) and ast.get('nodeType') == 'SourceUnit', ast, 'root must be SourceUnit')
    visit(ast)


def main():
    system = platform.system()
    if system not in PINS:
        raise ValueError(f'unsupported compiler platform: {system}')
    pin = PINS[system]
    source = pathlib.Path(sys.argv[1]).resolve(strict=True)
    if not source.is_relative_to(ROOT.resolve(strict=True)):
        raise ValueError('source outside package')
    if source != (ROOT / SOURCE).resolve(strict=True):
        raise ValueError('unregistered source or source outside package')
    raw = source.read_bytes()
    binary = ROOT / '.lake/solidity-import/solc'
    if digest(binary.read_bytes()) != pin:
        raise ValueError('compiler checksum mismatch')
    version = subprocess.check_output([str(binary), '--version']).decode()
    if '0.8.33+commit.64118f21.' not in version:
        raise ValueError('compiler version mismatch')
    inp = dict(language='Solidity', sources={SOURCE: {'content': raw.decode()}}, settings=SETTINGS)
    encoded = json.dumps(inp, sort_keys=True).encode()
    key = digest(encoded + pin.encode())
    cache = binary.parent / (key + '.json')
    if cache.exists():
        record = json.loads(cache.read_text())
        out = record['output']
        if record['key'] != key or record['digest'] != digest(json.dumps(out, sort_keys=True).encode()):
            raise ValueError('corrupt AST cache')
    else:
        p = subprocess.run([str(binary), '--standard-json', '--no-import-callback'],
                           input=encoded, capture_output=True, check=True)
        out = json.loads(p.stdout)
        if any(e['severity'] == 'error' for e in out.get('errors', [])):
            raise ValueError('\n'.join(e['formattedMessage'] for e in out['errors']))
        record = dict(key=key, output=out, digest=digest(json.dumps(out, sort_keys=True).encode()))
        tmp = cache.with_suffix('.tmp')
        tmp.write_text(json.dumps(record, sort_keys=True))
        tmp.replace(cache)
    if set(out['sources']) != {SOURCE}:
        raise ValueError('unexpected compiler sources')
    ast = out['sources'][SOURCE]['ast']
    def fail(n, why):
        start, size, sid = map(int, n['src'].split(':'))
        if sid != out['sources'][SOURCE]['id']:
            raise ValueError('unexpected source id')
        prefix = raw[:start]
        line = prefix.count(b'\n') + 1
        column = len(prefix.rsplit(b'\n', 1)[-1]) + 1
        excerpt = raw[start:start + min(size, 100)].decode(errors='replace')
        raise ValueError(f'{SOURCE}:{line}:{column}: {n["nodeType"]}: {why}\n{excerpt}')
    def need(ok, n, why):
        if not ok:
            fail(n, why)
    def ident(n):
        name = n['name']
        need(re.fullmatch(r'[A-Za-z][A-Za-z0-9_]*', name) and name != 'sourceDigest', n, 'unsupported/reserved name')
        return name
    validate_ast(ast, need)
    contracts = []
    for n in ast['nodes']:
        if n['nodeType'] == 'PragmaDirective':
            need(n['literals'][0] == 'solidity', n, 'unsupported pragma')
        elif n['nodeType'] == 'ContractDefinition':
            contracts.append(n)
        else:
            fail(n, 'unsupported source declaration')
    need(len(contracts) == 1, ast, 'exactly one concrete contract required')
    c = contracts[0]
    need(c['contractKind'] == 'contract' and not c['abstract'] and not c['baseContracts'], c, 'inheritance/abstract contract unsupported')
    layout = out['contracts'][SOURCE][c['name']]['storageLayout']
    entries = {x['astId']: x for x in layout['storage']}
    fields, funcs, errors = {}, [], {}
    for n in c['nodes']:
        kind = n['nodeType']
        if kind == 'VariableDeclaration':
            name = ident(n)
            need(n['stateVariable'] and not n['constant'] and n['mutability'] == 'mutable' and n.get('value') is None and n['storageLocation'] == 'default', n, 'initializer/constant/transient field unsupported')
            typ = n['typeDescriptions']['typeString']
            need(typ in ('uint256', 'mapping(address => uint256)'), n, 'unsupported storage type')
            e = entries.get(n['id'])
            need(e is not None and e['offset'] == 0, n, 'missing/packed layout')
            t = layout['types'][e['type']]
            need(t['numberOfBytes'] == '32', n, 'nonword layout')
            if typ == 'uint256':
                need(t['encoding'] == 'inplace' and t['label'] == typ, n, 'bad scalar layout')
            else:
                need(t['encoding'] == 'mapping' and layout['types'][t['key']]['label'] == 'address' and layout['types'][t['value']]['label'] == 'uint256', n, 'bad mapping layout')
            fields[n['id']] = dict(id=n['id'], name=name + 'Slot', getter=name if n['visibility'] == 'public' else None, slot=int(e['slot']), mapping=typ.startswith('mapping'))
        elif kind == 'ErrorDefinition':
            need(not n['parameters']['parameters'], n, 'only zero-argument custom errors')
            errors[n['id']] = ident(n)
        elif kind == 'FunctionDefinition':
            funcs.append(n)
        else:
            fail(n, 'unsupported contract declaration')
    need(set(entries) == set(fields), c, 'unaccounted layout field')
    def ty(n):
        t = n['typeDescriptions']['typeString']
        need(t in ('uint256', 'address'), n, 'unsupported value type')
        return t
    def expr(n, scope):
        k = n['nodeType']
        if k == 'Identifier':
            rid = n['referencedDeclaration']
            if rid in scope:
                need(ty(n) == scope[rid], n, 'reference type mismatch')
                return ['local', rid]
            need(rid in fields and not fields[rid]['mapping'], n, 'unresolved/non-scalar reference')
            return ['read', rid]
        if k == 'MemberAccess':
            b = n['expression']
            need(n['memberName'] == 'sender' and b['nodeType'] == 'Identifier' and b['name'] == 'msg' and b['referencedDeclaration'] < 0 and ty(n) == 'address', n, 'only builtin msg.sender supported')
            return ['sender']
        if k == 'IndexAccess':
            b = n['baseExpression']
            need(b['nodeType'] == 'Identifier' and b['referencedDeclaration'] in fields and fields[b['referencedDeclaration']]['mapping'], n, 'unsupported index base')
            need(ty(n['indexExpression']) == 'address' and ty(n) == 'uint256', n, 'bad mapping index/value type')
            return ['map', b['referencedDeclaration'], expr(n['indexExpression'], scope)]
        if k == 'Literal':
            need(n['kind'] == 'number' and not n.get('subdenomination') and re.fullmatch('[0-9]+', n['value']) and int(n['value']) < 2**256, n, 'unsupported literal')
            return ['number', int(n['value'])]
        if k == 'BinaryOperation':
            need(n['operator'] in ('+', '-', '<') and ty(n['leftExpression']) == 'uint256' and ty(n['rightExpression']) == 'uint256', n, 'unsupported binary operation/types')
            return [n['operator'], expr(n['leftExpression'], scope), expr(n['rightExpression'], scope)]
        fail(n, 'unsupported expression')
    def statements(nodes, scope, returns):
        result = []
        for i, n in enumerate(nodes):
            k = n['nodeType']
            if k == 'ExpressionStatement':
                a = n['expression']
                need(a['nodeType'] == 'Assignment' and a['operator'] in ('=', '+=', '-='), n, 'unsupported expression statement')
                lhs = expr(a['leftHandSide'], scope)
                need(lhs[0] in ('read', 'map'), a, 'only storage assignment supported')
                rhs = expr(a['rightHandSide'], scope)
                result.append(['write', lhs, a['operator'], rhs])
            elif k == 'VariableDeclarationStatement':
                ds = n['declarations']
                need(len(ds) == 1 and ds[0] is not None and n['initialValue'] is not None, n, 'unsupported locals')
                d = ds[0]
                need(ty(d) == 'uint256', d, 'only uint256 locals')
                value = expr(n['initialValue'], scope)
                scope = dict(scope, **{})
                scope[d['id']] = ty(d)
                result.append(['let', d['id'], value])
            elif k == 'IfStatement':
                need(n.get('falseBody') is None and n['trueBody']['nodeType'] == 'Block', n, 'only if/revert guard supported')
                body = n['trueBody']['statements']
                need(len(body) == 1 and body[0]['nodeType'] == 'RevertStatement', n, 'only if/revert guard supported')
                call = body[0]['errorCall']
                callee = call['expression']
                need(callee['nodeType'] == 'Identifier' and callee['referencedDeclaration'] in errors and not call['arguments'], n, 'unsupported revert')
                condition = expr(n['condition'], scope)
                need(condition[0] == '<', n, 'only uint256 comparison guard supported')
                # Match Verity's zero-argument custom-error display convention.
                result.append(['guard', condition, errors[callee['referencedDeclaration']] + '()'])
            elif k == 'Return':
                need(i == len(nodes)-1 and returns == 'uint256' and n['expression'] is not None, n, 'only terminal scalar return')
                result.append(['return', expr(n['expression'], scope)])
            else:
                fail(n, 'unsupported statement')
        if returns != 'unit':
            need(result and result[-1][0] == 'return', c, 'missing terminal return')
        return result
    output = []
    for f in funcs:
        name = ident(f)
        need(f['kind'] == 'function' and f['implemented'] and not f['modifiers'] and not f['virtual'] and not f.get('overrides') and f['visibility'] in ('external', 'public') and f['stateMutability'] in ('nonpayable', 'view'), f, 'unsupported function surface')
        ps = f['parameters']['parameters']
        rs = f['returnParameters']['parameters']
        need(len(ps) <= 1 and len(rs) <= 1 and all(not r['name'] and ty(r) == 'uint256' for r in rs), f, 'unsupported signature')
        params = [dict(id=p['id'], name=ident(p), type=ty(p)) for p in ps]
        returns = 'uint256' if rs else 'unit'
        output.append(dict(name=name, params=params, returns=returns, body=statements(f['body']['statements'], {p['id']: p['type'] for p in params}, returns)))
    names = [f['name'] for f in fields.values()] + [f['getter'] for f in fields.values() if f['getter']] + [f['name'] for f in output] + ['sourceDigest']
    need(len(names) == len(set(names)), c, 'overload/generated name collision')
    print(json.dumps(dict(fields=list(fields.values()), functions=output,
                         digest=digest(json.dumps(dict(input=inp, output=out,
                             pythonImporter=digest(pathlib.Path(__file__).read_bytes()),
                             leanImporter=digest((ROOT / 'Contracts/VaultFromSolidity/Importer/SolidityImporter.lean').read_bytes()),
                             compilerSha256=pin, compilerVersion=version), sort_keys=True).encode()))))

if __name__ == '__main__':
    try:
        main()
    except (ValueError, KeyError, OSError, subprocess.CalledProcessError) as e:
        print(str(e), file=sys.stderr)
        sys.exit(1)
