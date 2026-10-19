"""Regression tests for fail-closed coverage accounting."""
import tempfile
import json
import io
import tarfile
import hashlib
import base64
from unittest.mock import patch
from subprocess import CompletedProcess
import unittest
from pathlib import Path

import re

from solidity_import_coverage import classify, position, spelling, summarize, checkout, MeasurementError, inventory, dependencies, probe, refresh_report, main, milestone_summary, excluded_functions, markdown, MANIFEST
from solidity_import_coverage import IMPORTER_SOLC, IMPORTER_DEFAULT_SOLC, importer_compiler, pragma_at, matrix_entry, compiler_matrix, measure

REPO = Path(__file__).resolve().parents[1]
V34, V10 = '0.8.34+commit.80d5c536', '0.8.10+commit.fc410830'


class CoverageTests(unittest.TestCase):
    def test_real_diagnostic_preserves_location_and_reason(self):
        result = classify(1, 'Probe.lean:2:0: error: src/Lib.sol:41:9: ForStatement: '
                          '[solidity-import:unsupported] loops not supported\nclosure: C.f -> L.g')
        self.assertEqual(result, {'status': 'rejected', 'blocker': {
            'file': 'src/Lib.sol', 'line': 41, 'column': 9,
            'construct': 'ForStatement', 'reason': 'loops not supported'}})

    def test_compiler_version_is_rejected_but_crashes_are_unknown(self):
        result = classify(1, 'solc: ParserError: Source file requires different compiler version '
                          f'(current compiler is {V34}.Linux.g++)\n --> contracts/Old.sol:2:1:\n')
        self.assertEqual(result['status'], 'rejected')
        self.assertEqual(result['blocker']['construct'], 'PragmaDirective')
        self.assertEqual(classify(1, 'solc failed: signal 11')['status'], 'error')

    def test_missing_tool_and_missing_success_marker_are_not_successes(self):
        for code, text in [(127, 'lake: not found'), (0, ''), (1, 'COVERAGE_IMPORT_OK')]:
            self.assertEqual(classify(code, text)['status'], 'error')
        self.assertEqual(classify(0, 'COVERAGE_IMPORT_OK\n')['status'], 'importable')

    def test_unknowns_cannot_raise_percentage_or_histogram(self):
        good = {'status': 'importable'}
        bad = {'status': 'rejected', 'blocker': {'construct': 'ForStatement', 'reason': 'loop'}}
        unknown = {'status': 'error'}
        result = summarize([good, bad, bad, unknown])
        self.assertEqual(result['percent_importable'], 25)
        self.assertEqual(result['first_blocker_histogram'], [{'blocker': 'ForStatement: loop', 'functions': 2}])
        self.assertFalse(result['complete'])
        self.assertIsNone(summarize([])['percent_importable'])
        self.assertFalse(summarize([])['complete'])

    def test_offsets_count_bytes_as_importer_does(self):
        self.assertEqual(position('// é\nf()', '6:3:0'), {'line': 2, 'column': 1})

    def test_array_and_qualified_struct_types_are_not_dropped(self):
        t = {'nodeType': 'ArrayTypeName', 'baseType': {
            'nodeType': 'UserDefinedTypeName', 'pathNode': {'name': 'I.Market'}}, 'length': None}
        self.assertEqual(spelling(t, ''), 'I.Market[]')

    def test_inventory_includes_inherited_helpers_and_prefers_override(self):
        def fn(name, ident):
            return {'id': ident, 'nodeType': 'FunctionDefinition', 'kind': 'function',
                    'name': name, 'body': {}, 'parameters': {'parameters': []},
                    'visibility': 'internal', 'src': '0:1:0'}
        base = {'id': 1, 'nodeType': 'ContractDefinition', 'name': 'Base',
                'nodes': [fn('overridden', 3), fn('inherited', 4)]}
        child = {'id': 2, 'nodeType': 'ContractDefinition', 'name': 'Child',
                 'linearizedBaseContracts': [2, 1], 'nodes': [fn('overridden', 5)]}
        result = {'sources': {'Base.sol': {'ast': {'nodes': [base]}},
                              'Child.sol': {'ast': {'nodes': [child]}}}}
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp).resolve()
            (root / 'Base.sol').write_text('base')
            (root / 'Child.sol').write_text('child')
            with patch('solidity_import_coverage.checked', return_value=json.dumps(result)):
                rows = inventory({'inventory_solc': '0.8.34'},
                                 {'entry': 'Child.sol', 'contract': 'Child'}, root, 'solc', root)
            self.assertEqual([(r['name'], r['declaring_contract']) for r in rows],
                             [('overridden', 'Child'), ('inherited', 'Base')])
            self.assertEqual(rows[1]['file'], 'Base.sol')

    def test_receive_and_fallback_have_distinct_identities(self):
        functions = [{'nodeType': 'FunctionDefinition', 'kind': kind, 'name': '', 'body': {},
                      'parameters': {'parameters': []}, 'visibility': 'external', 'src': '0:1:0'}
                     for kind in ('receive', 'fallback')]
        contract = {'id': 1, 'nodeType': 'ContractDefinition', 'name': 'C',
                    'linearizedBaseContracts': [1], 'nodes': functions}
        result = {'sources': {'C.sol': {'ast': {'nodes': [contract]}}}}
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp).resolve()
            (root / 'C.sol').write_text('C')
            with patch('solidity_import_coverage.checked', return_value=json.dumps(result)):
                rows = inventory({'inventory_solc': '0.8.34'}, {'entry': 'C.sol', 'contract': 'C'},
                                 root, 'solc', root)
            self.assertEqual([r['signature'] for r in rows], ['receive()', 'fallback()'])

    def test_wrong_private_root_cannot_count_as_importable(self):
        fn = {'kind': 'function', 'name': 'helper', 'types': [], 'declaring_contract': 'Base',
              'file': 'Base.sol', 'line': 9, 'column': 5}
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp).resolve()
            with patch('solidity_import_coverage.run', return_value=CompletedProcess([], 0, 'COVERAGE_WRONG_ROOT', '')):
                result = probe(fn, {'entry': 'Child.sol', 'contract': 'Child'}, root, root, root, 10)
            self.assertEqual(result['status'], 'rejected')
            self.assertEqual(result['blocker']['file'], 'Base.sol')
            self.assertIn('different declaring contract', result['blocker']['reason'])
            self.assertIn('root.contract != "Base"', (root / 'Probe.lean').read_text())
            wrong_failure = ('Child.sol:3:4: ForStatement: [solidity-import:unsupported] loop\n'
                             'closure: Child.helper')
            with patch('solidity_import_coverage.run', return_value=CompletedProcess([], 1, wrong_failure, '')):
                result = probe(fn, {'entry': 'Child.sol', 'contract': 'Child'}, root, root, root, 10)
            self.assertEqual(result['blocker']['construct'], 'Inheritance')
            self.assertEqual(result['blocker']['file'], 'Base.sol')

    def test_partial_campaign_cannot_be_complete(self):
        one = {'project': 'p', 'entry': 'One.sol', 'contract': 'One'}
        two = {'project': 'p', 'entry': 'Two.sol', 'contract': 'Two'}
        rows = [{'status': 'importable'}]
        measured = {**one, 'functions': rows, 'summary': summarize(rows)}
        report = {'expected_contracts': [one, two], 'contracts': [measured]}
        refresh_report(report)
        self.assertFalse(report['complete'])
        self.assertEqual(report['pending'], [two])
        self.assertIsNone(report['summary']['percent_importable'])
        report['contracts'].append({**two, 'functions': rows, 'summary': summarize(rows)})
        refresh_report(report)
        self.assertTrue(report['complete'])
        self.assertEqual(report['summary']['percent_importable'], 100)

    def test_build_failure_replaces_stale_success_artifact(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp).resolve()
            manifest = root / 'manifest.json'
            manifest.write_text(json.dumps({'scope': 'test', 'projects': [{
                'id': 'p', 'contracts': [{'entry': 'C.sol', 'contract': 'C'}]}]}))
            output = root / 'report'
            output.mkdir()
            (output / 'coverage.json').write_text('{"complete": true}')
            def fail_build(*args, **kwargs):
                snapshot = json.loads((output / 'coverage.json').read_text())
                self.assertFalse(snapshot['complete'])
                self.assertEqual(len(snapshot['pending']), 1)
                return CompletedProcess([], 1, 'build failed', '')
            argv = ['coverage', '--manifest', str(manifest), '--workspace', str(root),
                    '--output', str(output)]
            with patch('sys.argv', argv), patch('solidity_import_coverage.checked', return_value='head'), \
                    patch('solidity_import_coverage.run', side_effect=fail_build):
                self.assertEqual(main(), 1)
            self.assertFalse(json.loads((output / 'coverage.json').read_text())['complete'])

    def test_dependency_tampering_is_an_error(self):
        archive = io.BytesIO()
        with tarfile.open(fileobj=archive, mode='w:gz') as tar:
            info = tarfile.TarInfo('package/C.sol')
            info.size = 1
            tar.addfile(info, io.BytesIO(b'C'))
        data = archive.getvalue()
        integrity = 'sha512-' + base64.b64encode(hashlib.sha512(data).digest()).decode()
        project = {'dependencies': [{'package': '@test/core', 'integrity': integrity}]}
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp).resolve()
            (root / 'archives').mkdir()
            (root / 'archives' / (hashlib.sha256(integrity.encode()).hexdigest() + '.tgz')).write_bytes(data)
            dependencies(project, root, root, False)
            (root / 'node_modules/@test/core/C.sol').write_bytes(b'X')
            with self.assertRaisesRegex(MeasurementError, 'differs from pinned archive'):
                dependencies(project, root, root, False)

    def test_unpinned_sources_rejected_before_fetch(self):
        with tempfile.TemporaryDirectory() as tmp:
            with self.assertRaisesRegex(MeasurementError, 'full commit SHA'):
                checkout({'id': 'test', 'commit': 'main'}, Path(tmp), True)

    def test_probe_uses_target_profile_when_present(self):
        fn = {'kind': 'function', 'name': 'getApr', 'types': [], 'declaring_contract': 'IdleCreditVault',
              'file': 'contracts/strategies/idle/IdleCreditVault.sol', 'line': 10, 'column': 5}
        target = {'entry': 'contracts/strategies/idle/IdleCreditVault.sol', 'contract': 'IdleCreditVault',
                  'profile': {'solc': '0.8.10+commit.fc410830', 'evmVersion': 'london',
                              'viaIR': False, 'optimizerRuns': 999999, 'bytecodeHash': 'none'}}
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp).resolve()
            with patch('solidity_import_coverage.run', return_value=CompletedProcess([], 0, 'COVERAGE_IMPORT_OK\n', '')):
                result = probe(fn, target, root, root, root, 10)
            self.assertEqual(result['status'], 'importable')
            probe_text = (root / 'Probe.lean').read_text()
            self.assertIn('solc := "0.8.10+commit.fc410830"', probe_text)
            self.assertIn('evmVersion := "london"', probe_text)
            self.assertIn('viaIR := false', probe_text)
            self.assertIn('optimizerRuns := some 999999', probe_text)

    def test_exclude_functions_milestone_is_manifest_driven(self):
        rows = [{'name': 'multicall', 'status': 'rejected',
                 'blocker': {'construct': 'X', 'reason': 'y'}},
                {'name': 'supply', 'status': 'importable'},
                {'name': 'withdraw', 'status': 'error'}]
        self.assertIsNone(milestone_summary({'id': 'any'}, rows))
        self.assertIsNone(milestone_summary({'id': 'any', 'exclude_functions': []}, rows))
        m = milestone_summary({'id': 'any', 'exclude_functions': ['multicall']}, rows)
        self.assertEqual(m['excluded_functions'], ['multicall'])
        self.assertEqual((m['functions'], m['importable'], m['errors']), (2, 1, 1))
        self.assertFalse(m['complete'])
        self.assertEqual(m['first_blocker_histogram'], [])
        report = {'scope': 's', 'complete': False, 'summary': {'first_blocker_histogram': []},
                  'contracts': [{'project': 'any', 'contract': 'C', 'functions': [],
                                 'summary': summarize(rows), 'milestone': m}]}
        self.assertIn('any:C milestone (excluding only `multicall`): 1/2; unknown: 1.',
                      markdown(report))

    def test_exclude_functions_must_be_distinct_names(self):
        for bad in ('multicall', [''], [1], ['a', 'a']):
            with self.assertRaisesRegex(ValueError, 'exclude_functions'):
                excluded_functions({'id': 'any', 'exclude_functions': bad})

    def test_manifest_exclusions_are_data_not_code(self):
        manifest = json.loads(MANIFEST.read_text())
        for project in manifest['projects']:
            excluded_functions(project)
        source = (Path(__file__).parent / 'solidity_import_coverage.py').read_text()
        for project in manifest['projects']:
            self.assertNotIn(f"== '{project['id']}'", source)
        midnight = [p for p in manifest['projects'] if p['id'] == 'midnight']
        self.assertEqual([p.get('exclude_functions') for p in midnight], [['multicall']])



def version_error(file, start, release=V34):
    return {'severity': 'error', 'sourceLocation': {'file': file, 'start': start, 'end': start + 1},
            'message': 'Source file requires different compiler version (current compiler is '
                       + release + '.Linux.g++)',
            'formattedMessage': 'ParserError: Source file requires different compiler version'}


def pragma_log(file, line, release=V34):
    return ('Probe.lean:2:0: error: solc: ParserError: Source file requires different compiler '
            f'version (current compiler is {release}.Linux.g++)\n --> {file}:{line}:1:\n')


class CompilerMatrixTests(unittest.TestCase):
    def test_pinned_releases_match_importer_and_manifest(self):
        imported = (REPO / 'Compiler/SolidityImport/Import.lean').read_text()
        block = imported[imported.index('private def solcReleases'):imported.index('private def resolveSolcRelease')]
        releases = re.findall(r'longVersion := "([^"]+)"', block)
        self.assertEqual(sorted(releases), sorted(IMPORTER_SOLC.values()))
        manifest = json.loads(MANIFEST.read_text())
        for version, release in IMPORTER_SOLC.items():
            self.assertTrue(release.startswith(version + '+commit.'))
            hosts = manifest['compilers'][version]
            entry = block[block.index(f'longVersion := "{release}"'):]
            entry = entry[:entry.index('supportsViaIR')]
            self.assertEqual(sorted(re.findall(r'"([0-9a-f]{64})"', entry)),
                             sorted(h['sha256'] for h in hosts.values()))
            for host in hosts.values():
                self.assertIn('v' + release, host['path'])
        profile = (REPO / 'Compiler/SolidityImport/Profile.lean').read_text()
        self.assertIn(f'solc : String := "{IMPORTER_DEFAULT_SOLC}"', profile)

    def test_selection_is_profile_or_importer_default_never_inferred(self):
        self.assertEqual(importer_compiler({'entry': 'C.sol', 'contract': 'C'}),
                         {'version': '0.8.34', 'release': V34, 'selected_by': 'importer default'})
        profiled = {'profile': {'solc': V10, 'evmVersion': 'london'}}
        self.assertEqual(importer_compiler(profiled),
                         {'version': '0.8.10', 'release': V10, 'selected_by': 'target profile'})
        # Near misses: unpinned release, short version, wrong commit, legacy pin.
        for near in ('0.8.11+commit.d7f03943', '0.8.34', '0.8.34+commit.80d5c537',
                     '0.5.16+commit.9c3226ce'):
            with self.assertRaisesRegex(MeasurementError, 'importer pins only'):
                importer_compiler({'profile': {'solc': near}})

    def test_matrix_entry_locates_version_pragma_exactly(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp).resolve()
            text = '// é\npragma solidity =0.5.16;\ncontract C {}\n'
            (root / 'C.sol').write_text(text)
            start = len('// é\n'.encode())
            row = matrix_entry('0.8.34', V34, {'errors': [version_error('C.sol', start)]}, root)
            self.assertEqual(row, {'version': '0.8.34', 'release': V34, 'status': 'version_rejected',
                                   'other_errors': 0, 'version_errors': [{
                                       'file': 'C.sol', 'line': 2, 'column': 1,
                                       'pragma': 'pragma solidity =0.5.16;'}]})
            self.assertEqual(matrix_entry('0.8.10', V10, {'errors': [
                {'severity': 'warning', 'message': 'w', 'formattedMessage': 'w'}]}, root)['status'],
                'accepted')
            other = matrix_entry('0.8.10', V10, {'errors': [
                {'severity': 'error', 'message': 'Undeclared identifier.',
                 'formattedMessage': 'DeclarationError: Undeclared identifier.'}]}, root)
            self.assertEqual(other['status'], 'rejected')
            self.assertNotIn('version_errors', other)
            unlocated = version_error('C.sol', 0)
            del unlocated['sourceLocation']
            with self.assertRaisesRegex(MeasurementError, 'without a source location'):
                matrix_entry('0.8.34', V34, {'errors': [unlocated]}, root)

    def test_pragma_location_near_misses_fail_closed(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp).resolve()
            (root / 'C.sol').write_text('pragma abicoder v2;\npragma solidity ^0.8.0;\ncontract C {}\n')
            self.assertEqual(pragma_at(root, 'C.sol', 2, 1), 'pragma solidity ^0.8.0;')
            for line, column in ((1, 1), (3, 1), (2, 2), (9, 1), (0, 1)):
                with self.assertRaisesRegex(MeasurementError, 'no version pragma'):
                    pragma_at(root, 'C.sol', line, column)
            with self.assertRaisesRegex(MeasurementError, 'escapes'):
                pragma_at(root, '../C.sol', 1, 1)

    def test_missing_matrix_compiler_is_a_measurement_error(self):
        manifest = json.loads(MANIFEST.read_text())
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp).resolve()
            with self.assertRaisesRegex(MeasurementError, 'missing inventory compiler'):
                compiler_matrix({'entry': 'C.sol', 'contract': 'C'}, root, manifest, root, False, root)

    def blocked(self, log, code=1, accepting=()):
        fns = [{'kind': 'function', 'name': n, 'types': [], 'declaring_contract': 'C',
                'file': 'C.sol', 'line': 3, 'column': 5} for n in ('f', 'g', 'h')]
        matrix = [{'version': '0.8.34', 'release': V34, 'status': 'version_rejected',
                   'version_errors': [{'file': 'C.sol', 'line': 1, 'column': 1,
                                       'pragma': 'pragma solidity =0.5.16;'}], 'other_errors': 0},
                  {'version': '0.8.10', 'release': V10,
                   'status': 'accepted' if V10 in accepting else 'version_rejected',
                   'version_errors': []}]
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp).resolve()
            (root / 'C.sol').write_text('pragma solidity =0.5.16;\nimport "./B.sol";\n')
            (root / 'B.sol').write_text('// SPDX\npragma solidity =0.5.16;\n')
            with patch('solidity_import_coverage.run',
                       return_value=CompletedProcess([], code, log, '')) as run:
                rows = measure(fns, {'entry': 'C.sol', 'contract': 'C'}, root, root, root, 10,
                               importer_compiler({}), matrix)
            self.assertEqual(run.call_count, 1)
        return rows

    def test_version_blocked_source_uses_one_importer_witness(self):
        # The importer submits the import closure; its first error may be an imported file.
        rows = self.blocked(pragma_log('B.sol', 2))
        self.assertEqual([r['status'] for r in rows], ['rejected'] * 3)
        self.assertEqual({(r['blocker']['file'], r['blocker']['line'], r['blocker']['column'])
                          for r in rows}, {('B.sol', 2, 1)})
        self.assertEqual(rows[0]['blocker']['reason'],
                         f'source pragma `pragma solidity =0.5.16;` rejected by importer solc {V34} '
                         '(importer default); pinned importer releases accepting the source: none')
        self.assertEqual([r['evidence'] for r in rows],
                         ['importer probe', 'importer probe of function 0', 'importer probe of function 0'])
        hinted = self.blocked(pragma_log('C.sol', 1), accepting=(V10,))
        self.assertTrue(hinted[0]['blocker']['reason'].endswith('accepting the source: ' + V10))

    def test_version_blocked_disagreement_is_unknown(self):
        for log, code in [('COVERAGE_IMPORT_OK\n', 0),                     # importer accepted
                          (pragma_log('C.sol', 1, V10), 1),                # stale compiler banner
                          (pragma_log('C.sol', 2), 1),                     # not a pragma location
                          ('C.sol:1:1: ForStatement: [solidity-import:unsupported] x\n', 1),
                          ('solc failed: signal 11', 1)]:
            rows = self.blocked(log, code)
            self.assertEqual([r['status'] for r in rows], ['error'] * 3, log)
            self.assertFalse(summarize(rows)['complete'])
            self.assertEqual(summarize(rows)['first_blocker_histogram'], [])

    def test_unreproduced_pragma_rejection_is_unknown(self):
        fn = {'kind': 'function', 'name': 'f', 'types': [], 'declaring_contract': 'C',
              'file': 'C.sol', 'line': 3, 'column': 5}
        matrix = [{'version': '0.8.34', 'release': V34, 'status': 'accepted'}]
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp).resolve()
            with patch('solidity_import_coverage.run',
                       return_value=CompletedProcess([], 1, pragma_log('C.sol', 1), '')):
                rows = measure([fn, fn], {'entry': 'C.sol', 'contract': 'C'}, root, root, root, 10,
                               importer_compiler({}), matrix)
        self.assertEqual([r['status'] for r in rows], ['error', 'error'])
        self.assertIn('does not reproduce', rows[0]['error'])

    def test_report_records_selection_and_incomplete_matrix(self):
        rows = [{'signature': 'f()', 'status': 'rejected', 'blocker': {
            'file': 'C.sol', 'line': 1, 'column': 1, 'construct': 'PragmaDirective', 'reason': 'r'}}]
        measured = {'project': 'p', 'entry': 'C.sol', 'contract': 'C', 'functions': rows,
                    'summary': summarize(rows), 'compiler': {
                        'inventory': '0.5.16', 'importer': importer_compiler({}),
                        'matrix': [{'release': V34, 'status': 'version_rejected'},
                                   {'release': V10, 'status': 'accepted'}]}}
        failed = {'project': 'p', 'entry': 'D.sol', 'contract': 'D', 'functions': [],
                  'error': 'missing inventory compiler', 'summary': summarize([])}
        report = {'scope': 's', 'importer_solc_releases': list(IMPORTER_SOLC.values()),
                  'expected_contracts': [{k: c[k] for k in ('project', 'entry', 'contract')}
                                         for c in (measured, failed)],
                  'contracts': [measured, failed]}
        refresh_report(report)
        self.assertFalse(report['complete'])
        self.assertIsNone(report['summary']['percent_importable'])
        text = markdown(report)
        self.assertIn(f'| p:C | 0.5.16 | {V34} (importer default) | {V10} |', text)
        self.assertIn('| p:D | unavailable | unavailable | unavailable |', text)
        self.assertIn(f'Importer-pinned solc releases: {V34}, {V10}.', text)


if __name__ == '__main__':
    unittest.main()
