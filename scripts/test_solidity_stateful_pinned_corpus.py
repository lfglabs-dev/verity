"""Corpus pinned-sequence configurations are complete and their prefixes are checked."""
import copy
import json
from pathlib import Path
import tempfile
import unittest

from solidity_differential import check_pinned_sequence_corpus as corpus
from solidity_differential import pinned_sequence as instrument
from solidity_differential.engine import HarnessError


def manifest():
    return json.loads(corpus.MANIFEST.read_text())


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


if __name__ == '__main__':
    unittest.main()
