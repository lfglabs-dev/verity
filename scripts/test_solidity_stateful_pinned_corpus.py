"""Corpus pinned-sequence configurations are complete and their prefixes are checked."""
import copy
import json
from pathlib import Path
import tempfile
import unittest
import unittest.mock

from solidity_differential import check_pinned_sequence_corpus as corpus
from solidity_differential import pinned_sequence as instrument
from solidity_differential.engine import HarnessError


def manifest():
    return json.loads(corpus.MANIFEST.read_text())


def solc_output(sequence):
    methods = {s: '00000000' for s in sequence['signatures']}
    return {'contracts': {sequence['entry']: {sequence['contract']: {
        'abi': [{'type': 'function'}], 'evm': {'methodIdentifiers': methods}}}}}


class CorpusSequences(unittest.TestCase):
    def test_committed_sequences_are_complete(self):
        pairs = corpus.corpus_sequences(manifest())
        self.assertTrue(pairs)
        for project, sequence in pairs:
            self.assertRegex(project['commit'], r'^[0-9a-f]{40}$')
            self.assertEqual(set(sequence['arguments']), set(sequence['signatures']))
            for signature in sequence['signatures']:
                instrument.argument_types(signature)
            statuses = {row['expect'] for row in sequence['prefix']}
            self.assertEqual(statuses, {'ok', 'revert'})

    def test_materialized_config_loads_with_pinned_revision(self):
        project, sequence = corpus.corpus_sequences(manifest())[0]
        with tempfile.TemporaryDirectory() as temp:
            path = corpus.materialize(project, sequence, temp, Path(temp))
            config = instrument.load_config(path)
        self.assertEqual(config['revision'], project['commit'])
        self.assertEqual(config['project'], Path(temp).resolve())
        target = '0x' + '12' * 20
        rows = instrument.transaction_sequence(config, 128, 2449, target)
        self.assertEqual(len(rows), 128)

    def mutated(self, change):
        data = manifest()
        project = next(p for p in data['projects'] if p.get('sequences'))
        change(project['sequences'][0])
        return data

    def test_prefix_step_without_expect_is_rejected(self):
        data = self.mutated(lambda s: s['prefix'][0].pop('expect'))
        with self.assertRaisesRegex(HarnessError, r'prefix steps \[0\] lack'):
            corpus.corpus_sequences(data)

    def test_signature_without_succeeding_step_is_rejected(self):
        def change(sequence):
            first = sequence['signatures'][0]
            sequence['prefix'] = [r for r in sequence['prefix'] if r['signature'] != first]
        with self.assertRaisesRegex(HarnessError, 'no succeeding prefix step'):
            corpus.corpus_sequences(self.mutated(change))

    def test_sequence_may_not_override_pin(self):
        data = self.mutated(lambda s: s.update(revision='0' * 40))
        with self.assertRaisesRegex(HarnessError, 'sequence keys'):
            corpus.corpus_sequences(data)

    def test_duplicate_contract_and_empty_selection_are_rejected(self):
        data = manifest()
        project = next(p for p in data['projects'] if p.get('sequences'))
        project['sequences'].append(copy.deepcopy(project['sequences'][0]))
        with self.assertRaisesRegex(HarnessError, 'distinct contracts'):
            corpus.corpus_sequences(data)
        with self.assertRaisesRegex(HarnessError, 'no corpus sequence'):
            corpus.corpus_sequences(manifest(), ['no-such-project'])

    def test_duplicate_signature_is_rejected(self):
        data = self.mutated(lambda s: s['signatures'].append(s['signatures'][0]))
        with self.assertRaisesRegex(HarnessError, 'duplicate imported signatures'):
            corpus.corpus_sequences(data)

    def test_entry_points_must_all_be_imported(self):
        _, sequence = corpus.corpus_sequences(manifest())[0]
        output = solc_output(sequence)
        corpus.check_entry_points(sequence, output)
        contract = output['contracts'][sequence['entry']][sequence['contract']]
        contract['evm']['methodIdentifiers']['permit()'] = '00000000'
        with self.assertRaisesRegex(HarnessError, r"missing \['permit\(\)'\]"):
            corpus.check_entry_points(sequence, output)

    def test_receive_and_fallback_are_rejected(self):
        _, sequence = corpus.corpus_sequences(manifest())[0]
        for kind in ('receive', 'fallback'):
            output = solc_output(sequence)
            output['contracts'][sequence['entry']][sequence['contract']]['abi'].append({'type': kind})
            with self.assertRaisesRegex(HarnessError, f"unsupported \\['{kind}'\\]"):
                corpus.check_entry_points(sequence, output)


class RunSequence(unittest.TestCase):
    """The checker's per-sequence order: entry points, positive campaign, mutant."""

    def setUp(self):
        self.project, self.sequence = corpus.corpus_sequences(manifest())[0]
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name)
        self.calls = []

    def run_with(self, output, positive=0, mutant=1, witness=('tx',)):
        def run(config, out, transactions, seed, attempts, mutant=None):
            self.calls.append(mutant)
            if mutant:
                out.mkdir(parents=True, exist_ok=True)
                (out / 'reduced.json').write_text(json.dumps(
                    {'deletion_minimal': True, 'transactions': list(witness)}))
                return mutant_result
            return positive
        mutant_result = mutant
        return corpus.run_sequence(self.project, self.sequence, 'config.json', self.root, 128, 2449,
                                   entry_points=lambda config, root: output, run=run)

    def test_incomplete_entry_points_stop_before_any_campaign(self):
        output = solc_output(self.sequence)
        output['contracts'][self.sequence['entry']][self.sequence['contract']]['evm'][
            'methodIdentifiers'].pop(self.sequence['signatures'][0])
        with self.assertRaisesRegex(HarnessError, 'signatures differ'):
            self.run_with(output)
        self.assertEqual(self.calls, [])

    def test_positive_then_mutant(self):
        summary = self.run_with(solc_output(self.sequence))
        self.assertEqual(self.calls, [None, 'drop-events'])
        self.assertEqual(summary['mutantWitness'], 1)

    def test_divergence_and_escaped_mutant_fail(self):
        with self.assertRaisesRegex(HarnessError, 'campaign diverged'):
            self.run_with(solc_output(self.sequence), positive=1)
        with self.assertRaisesRegex(HarnessError, 'mutant escaped'):
            self.run_with(solc_output(self.sequence), mutant=0)
        with self.assertRaisesRegex(HarnessError, 'minimal witness'):
            self.run_with(solc_output(self.sequence), witness=())


class PrefixExpectations(unittest.TestCase):
    prefix = [{'signature': 'f()', 'expect': 'ok'}, {'signature': 'g()'},
              {'signature': 'h()', 'expect': 'revert'}]

    def test_matching_outcomes_pass(self):
        instrument.check_prefix_expectations(
            self.prefix, [{'status': 'ok'}, {'status': 'revert'}, {'status': 'revert'},
                          {'status': 'ok'}])

    def test_mismatch_is_located(self):
        with self.assertRaisesRegex(HarnessError, r'prefix step 2 \(h\(\)\): source route ok, expected revert'):
            instrument.check_prefix_expectations(
                self.prefix, [{'status': 'ok'}, {'status': 'ok'}, {'status': 'ok'}])

    def test_invalid_expect_is_rejected_at_load(self):
        project, sequence = corpus.corpus_sequences(manifest())[0]
        sequence = copy.deepcopy(sequence)
        sequence['prefix'][0]['expect'] = 'success'
        with tempfile.TemporaryDirectory() as temp:
            path = corpus.materialize(project, sequence, temp, Path(temp))
            with self.assertRaisesRegex(HarnessError, 'prefix step 0: expect'):
                instrument.load_config(path)


def dependent():
    """The committed project and its first sequence that deploys a dependency."""
    for project, sequence in corpus.corpus_sequences(manifest()):
        if sequence.get('dependencies'):
            return project, sequence
    raise AssertionError('no corpus sequence deploys a dependency')


class Dependencies(unittest.TestCase):
    def mutated(self, change):
        data = manifest()
        for project in data['projects']:
            for sequence in project.get('sequences', []):
                if sequence.get('dependencies'):
                    change(project, sequence)
                    return data
        raise AssertionError('no dependent sequence')

    def test_dependency_must_be_a_validated_sibling_with_its_settings(self):
        def unknown(project, sequence):
            sequence['dependencies'][0]['contract'] = 'Absent'
        with self.assertRaisesRegex(HarnessError, 'must be another sequence'):
            corpus.corpus_sequences(self.mutated(unknown))

        def itself(project, sequence):
            sequence['dependencies'][0]['contract'] = sequence['contract']
        with self.assertRaisesRegex(HarnessError, 'must be another sequence'):
            corpus.corpus_sequences(self.mutated(itself))

        def settings(project, sequence):
            sequence['settings'] = {**sequence['settings'], 'viaIR': False}
        with self.assertRaisesRegex(HarnessError, 'must share the settings'):
            corpus.corpus_sequences(self.mutated(settings))

        def extra(project, sequence):
            sequence['dependencies'][0]['entry'] = 'x.sol'
        with self.assertRaisesRegex(HarnessError, 'dependency keys'):
            corpus.corpus_sequences(self.mutated(extra))

    def test_materialized_dependency_takes_its_validated_imports(self):
        project, sequence = dependent()
        with tempfile.TemporaryDirectory() as temp:
            config = instrument.load_config(corpus.materialize(project, sequence, temp, Path(temp)))
        dependency = config['dependencies'][0]
        validated = next(s for s in project['sequences'] if s['contract'] == dependency['contract'])
        self.assertEqual(dependency['entry'], validated['entry'])
        self.assertEqual(dependency['signatures'], validated['signatures'])
        self.assertNotIn('rejected', config)
        # The tested contract is deployed after its dependency; blocks shift by one.
        rows = instrument.transaction_sequence(config, len(config['prefix']), 2449, '0x' + '12' * 20)
        self.assertEqual(rows[0]['blockNumber'], 3)
        driver = instrument.driver_source(Path(temp), config)
        mutant = instrument.driver_source(Path(temp), config, 'drop-events')
        self.assertIn('import Compiler.SolidityImport.ModelResponders\n', driver)
        self.assertIn(f'solidity_import dependency0 ', driver)
        self.assertIn(f'  contract {dependency["contract"]}\n', driver)
        self.assertIn('ModelResponders.configure', driver)
        self.assertIn('[dependency0.model])', driver)
        self.assertEqual(driver.split('def model')[0], mutant.split('def model')[0])
        self.assertEqual(driver.split('def main')[1], mutant.split('def main')[1])

    def test_rejected_functions_are_entry_points_and_never_imported(self):
        _, sequence = dependent()
        rejected = [row['signature'] for row in sequence['rejected']]
        self.assertTrue(rejected)
        output = solc_output(sequence)
        methods = output['contracts'][sequence['entry']][sequence['contract']]['evm']['methodIdentifiers']
        methods.update({signature: '00000000' for signature in rejected})
        corpus.check_entry_points(sequence, output)
        del methods[rejected[0]]
        with self.assertRaisesRegex(HarnessError, 'unknown'):
            corpus.check_entry_points(sequence, output)

        def imported(project, sequence):
            sequence['rejected'][0]['signature'] = sequence['signatures'][0]
        with self.assertRaisesRegex(HarnessError, 'distinct and not imported'):
            corpus.corpus_sequences(Dependencies.mutated(self, imported))

        def unlocated(project, sequence):
            sequence['rejected'][0]['rejection'] = ''
        with self.assertRaisesRegex(HarnessError, 'signature and its rejection'):
            corpus.corpus_sequences(Dependencies.mutated(self, unlocated))


class Rejections(unittest.TestCase):
    """Each rejected function alone must fail with exactly its located first error line."""

    def setUp(self):
        project, sequence = dependent()
        self.rejected = sequence['rejected'][:2]
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name)
        self.config = corpus.materialize(project, sequence, self.root, self.root)
        loaded = instrument.load_config(self.config)
        _, self.lines = corpus.rejection_source(loaded, self.rejected)
        # The pinned-source check runs against the real checkout; it is not under test here.
        self.patch = unittest.mock.patch.object(corpus, 'pinned_sources', lambda *args: None)
        self.patch.start()
        self.addCleanup(self.patch.stop)

    def fake_lean(self, errors, code=1):
        script = self.root / 'lean.sh'
        lines = ''.join(f'echo "$1:{line}:0: error: {message}"\n' for line, message in errors)
        script.write_text('#!/bin/sh\n' + lines + f'echo "closure: trailing detail"\nexit {code}\n')
        script.chmod(0o755)
        return (str(script),)

    def check(self, errors, code=1):
        out = self.root / 'out'
        out.mkdir(exist_ok=True)
        corpus.check_rejections(self.config, self.rejected, out, lean=self.fake_lean(errors, code))

    def test_exact_located_rejections_pass(self):
        self.check([(line, row['rejection']) for line, row in zip(self.lines, self.rejected)])

    def test_changed_message_missing_error_or_success_fail(self):
        good = [(line, row['rejection']) for line, row in zip(self.lines, self.rejected)]
        with self.assertRaisesRegex(HarnessError, 'rejection differs'):
            self.check([good[0], (good[1][0], 'other.sol:1:1: X: [solidity-import:unsupported] y')])
        with self.assertRaisesRegex(HarnessError, 'errors at lines'):
            self.check(good[:1])
        with self.assertRaisesRegex(HarnessError, 'errors at lines'):
            self.check(good, code=0)
        with self.assertRaisesRegex(HarnessError, 'rejection differs'):
            self.check(good + [(good[0][0], 'second error')])


class DeploymentWorld(unittest.TestCase):
    def test_nonce_addresses(self):
        deployer = instrument.SENDERS[0]
        self.assertEqual(instrument.create_address(deployer, 1),
                         '0xe7f1725e7734ce288f8367e1bb143e90bb3f0512')
        self.assertEqual(instrument.create_address(deployer, 0), instrument.create_address(deployer))
        with self.assertRaisesRegex(HarnessError, 'nonce'):
            instrument.create_address(deployer, 256)

    def test_mapping_entry_slot(self):
        layout = {'storage': [{'label': 'balances', 'slot': '3', 'offset': 0, 'type': 'm'}],
                  'types': {'m': {'encoding': 'mapping', 'key': 'a', 'value': 'u'},
                            'a': {'encoding': 'inplace', 'label': 'address', 'numberOfBytes': '20'},
                            'u': {'encoding': 'inplace', 'label': 'uint256', 'numberOfBytes': '32'}}}
        holder = '0x' + '12' * 20
        slot = instrument.storage_slot(layout, {'label': 'balances', 'keys': ['contract']},
                                       {'contract': holder})
        expected = instrument.keccak(bytes(12) + bytes.fromhex('12' * 20) + (3).to_bytes(32, 'big'))
        self.assertEqual(slot, int.from_bytes(expected, 'big'))
        with self.assertRaisesRegex(HarnessError, 'more keys'):
            instrument.storage_slot(layout, {'label': 'balances', 'keys': [holder, holder]}, {})
        with self.assertRaisesRegex(HarnessError, 'unknown deployed address'):
            instrument.storage_slot(layout, {'label': 'balances', 'keys': ['dependency:0']}, {})

    def test_deployed_immutables_are_read_back_consistently(self):
        code = '0x' + '00' * 4 + (7).to_bytes(32, 'big').hex() + (7).to_bytes(32, 'big').hex()
        refs = {'5': [{'start': 4, 'length': 32}, {'start': 36, 'length': 32}]}
        self.assertEqual(instrument.deployed_immutables(code, refs, {'5': 'X'}), {'X': 7})
        refs['5'][1]['start'] = 0
        with self.assertRaisesRegex(HarnessError, 'inconsistent'):
            instrument.deployed_immutables(code, refs, {'5': 'X'})

    def test_constructor_arguments_match_the_source_constructor(self):
        abi = [{'type': 'constructor', 'inputs': [{'type': 'address'}]}]
        holder = '0x' + '12' * 20
        self.assertEqual(instrument.constructor_arguments(abi, ['dependency:0'],
                                                          {'dependency:0': holder}, 'C'),
                         '00' * 12 + '12' * 20)
        with self.assertRaisesRegex(HarnessError, 'takes 1 arguments, 0 configured'):
            instrument.constructor_arguments(abi, [], {}, 'C')
        with self.assertRaisesRegex(HarnessError, 'takes 0 arguments'):
            instrument.constructor_arguments([], [1], {}, 'C')


class ProbeDeployment(unittest.TestCase):
    """Constructor writes must equal the configured initial storage of the deployed account."""

    def run_probe(self, post, status='0x1', moved=False):
        account = instrument.create_address(instrument.SENDERS[0])
        slot = '0x' + '00' * 31 + '03'
        tracers = []

        class Node:
            def __init__(self, directory):
                pass

            def __enter__(self):
                return self

            def __exit__(self, *unused):
                return False

            def rpc(self, method, *params):
                if method == 'eth_accounts':
                    return [instrument.SENDERS[0]]
                if method == 'debug_traceTransaction':
                    tracers.append(params[1])
                    return {'pre': {}, 'post': post(account, slot)}
                if method == 'eth_getCode':
                    return '0x60'
                raise AssertionError(method)

            def transact(self, request):
                return {'receipt': {'status': status, 'transactionHash': '0x01',
                                    'contractAddress': '0x' + '99' * 20 if moved else account}}

        initial = [[account, slot, '0x' + '00' * 31 + '05']]
        with unittest.mock.patch.object(instrument, 'Anvil', Node):
            result = instrument.probe_deployment(Path('unused'), [('C', account, '0x00')], initial)
        # Only a diff-mode prestate trace lists the constructor's post-state writes.
        self.assertEqual(tracers, [{'tracer': 'prestateTracer', 'tracerConfig': {'diffMode': True}}])
        return result

    def test_configured_write_passes_and_returns_runtime(self):
        self.assertEqual(self.run_probe(lambda a, s: {a: {'storage': {s: '0x05'}, 'nonce': 1}}),
                         ['0x60'])
        self.assertEqual(self.run_probe(lambda a, s: {a: {'nonce': 1}}), ['0x60'])

    def test_unconfigured_wrong_or_foreign_writes_fail(self):
        other = '0x' + '00' * 31 + '04'
        with self.assertRaisesRegex(HarnessError, 'constructor writes slot .* configured initial storage'):
            self.run_probe(lambda a, s: {a: {'storage': {other: '0x05'}}})
        with self.assertRaisesRegex(HarnessError, 'constructor writes slot'):
            self.run_probe(lambda a, s: {a: {'storage': {s: '0x06'}}})
        with self.assertRaisesRegex(HarnessError, 'foreign account'):
            self.run_probe(lambda a, s: {'0x' + '77' * 20: {'storage': {s: '0x05'}}})
        # A constructor that creates a contract changes that account's code and nonce.
        with self.assertRaisesRegex(HarnessError, 'foreign account'):
            self.run_probe(lambda a, s: {'0x' + '77' * 20: {'code': '0x00', 'nonce': 1}})
        with self.assertRaisesRegex(HarnessError, 'foreign account'):
            self.run_probe(lambda a, s: {instrument.SENDERS[0]: {'storage': {s: '0x05'}}})

    def test_fee_balances_may_move(self):
        self.assertEqual(self.run_probe(lambda a, s: {
            instrument.SENDERS[0]: {'balance': '0x1', 'nonce': 1},
            '0x' + '00' * 20: {'balance': '0x2'}, a: {'nonce': 1, 'code': '0x60'}}), ['0x60'])

    def test_failed_or_moved_deployment_fails(self):
        with self.assertRaisesRegex(HarnessError, 'deployment failed or moved'):
            self.run_probe(lambda a, s: {}, status='0x0')
        with self.assertRaisesRegex(HarnessError, 'deployment failed or moved'):
            self.run_probe(lambda a, s: {}, moved=True)


if __name__ == '__main__':
    unittest.main()
