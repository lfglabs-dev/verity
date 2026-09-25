"""Regression tests for fail-closed coverage accounting."""
import tempfile
import json
import io
import tarfile
import hashlib
import base64
from unittest.mock import patch
import unittest
from pathlib import Path

from solidity_import_coverage import classify, position, spelling, summarize, checkout, MeasurementError, inventory, dependencies


class CoverageTests(unittest.TestCase):
    def test_real_diagnostic_preserves_location_and_reason(self):
        result = classify(1, 'Probe.lean:2:0: error: src/Lib.sol:41:9: ForStatement: '
                          '[solidity-import:unsupported] loops not supported\nclosure: C.f -> L.g')
        self.assertEqual(result, {'status': 'rejected', 'blocker': {
            'file': 'src/Lib.sol', 'line': 41, 'column': 9,
            'construct': 'ForStatement', 'reason': 'loops not supported'}})

    def test_compiler_version_is_rejected_but_crashes_are_unknown(self):
        result = classify(1, 'solc: ParserError: Source file requires different compiler version\n'
                          ' --> contracts/Old.sol:2:1:\n')
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
            root = Path(tmp)
            (root / 'Base.sol').write_text('base')
            (root / 'Child.sol').write_text('child')
            with patch('solidity_import_coverage.checked', return_value=json.dumps(result)):
                rows = inventory({'inventory_solc': '0.8.34'},
                                 {'entry': 'Child.sol', 'contract': 'Child'}, root, 'solc', root)
            self.assertEqual([(r['name'], r['declaring_contract']) for r in rows],
                             [('overridden', 'Child'), ('inherited', 'Base')])
            self.assertEqual(rows[1]['file'], 'Base.sol')

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
            root = Path(tmp)
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


if __name__ == '__main__':
    unittest.main()
