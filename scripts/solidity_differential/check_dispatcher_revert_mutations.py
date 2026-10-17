"""Mutate each production dispatcher guard; kernel-check exact REVERT bytes.

Private clones preserve all body execution. Each mutant must compile separately,
fail the unchanged six quantified guard/frame laws, and change a separate minimal
kernel-reduced observation reproducibly. No refusal is scored as an EVM revert.
"""
import argparse
import hashlib
import json
import os
from pathlib import Path
from .engine import command, HarnessError


def main():
    root = Path(__file__).resolve().parents[2]
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, required=True)
    job = parser.parse_args().output.resolve()
    job.mkdir(parents=True, exist_ok=False)
    command(['lake', 'build', 'Contracts.SolidityImportSmoke.DispatcherRevertChecks'],
            cwd=root, timeout=1800, log=job / 'build.log')
    source = root / 'Compiler/Proofs/IRGeneration/IRInterpreter.lean'
    fixture = root / 'Contracts/SolidityImportSmoke/DispatcherRevertChecks.lean'
    text = source.read_text()
    legacy = text.split('noncomputable def interpretIR (', 1)[1].split(
        '/-- Contract-aware runtime interpretation', 1)[0]
    helpers = text.split('noncomputable def interpretIRWithInternals\n', 1)[1].split(
        '@[simp] theorem findInternalFunction?_eq_none_of_internalFunctions_nil', 1)[0]
    definitions = ('import Compiler.Proofs.IRGeneration.IRInterpreter\n'
        'namespace Compiler.Proofs.IRGeneration\n'
        'noncomputable def mutationInterpret (' + legacy +
        'noncomputable def mutationInterpretWithInternals\n' + helpers +
        'end Compiler.Proofs.IRGeneration\n')
    assert definitions.count('revertData := some []') == 6
    smoke = '\n'.join(fixture.read_text().splitlines()[1:])
    smoke = smoke.replace('interpretIRWithInternals', 'mutationInterpretWithInternals').replace(
        'interpretIR', 'mutationInterpret')
    files = [source, fixture, Path(__file__).resolve(), root / 'lean-toolchain',
             root / '.lake/build/lib/lean/Compiler/Proofs/IRGeneration/IRInterpreter.olean']
    identity = {str(p.relative_to(root)): hashlib.sha256(p.read_bytes()).hexdigest() for p in files}

    def unchanged():
        return identity == {str(p.relative_to(root)): hashlib.sha256(p.read_bytes()).hexdigest() for p in files}

    lean = str(Path(os.environ['LEAN_SYSROOT']) / 'bin/lean') if os.environ.get('LAKE_OVERRIDE_LEAN') == 'true' else 'lean'

    def run(name, impl, suffix):
        assert unchanged(), 'campaign inputs changed'
        path = job / (name + '.lean')
        path.write_text(impl + suffix)
        output = command(['lake', 'env', lean, str(path)], cwd=root, timeout=180,
                         log=job / (name + '.log'))
        assert unchanged(), 'campaign inputs changed'
        return output.splitlines()

    assert run('baseline-laws', definitions, smoke) == []
    offsets = [m for m in range(len(definitions)) if definitions.startswith('revertData := some []', m)]
    rows = []
    # Definition order: value, short args, selector miss; then helper-aware equivalents.
    for index, kind in enumerate(['nonpayable', 'short-args', 'unknown'] * 2):
        route = 'helpers' if index >= 3 else 'legacy'
        name = f'dispatch-{route}-{kind}-bytes-erased'
        offset = offsets[index]
        mutant = definitions[:offset] + definitions[offset:].replace('revertData := some []', 'revertData := none', 1)
        # Successful standalone elaboration is mandatory before scoring a law failure.
        assert run(name + '-compiled', mutant, '') == []
        try:
            run(name + '-laws', mutant, smoke)
        except HarnessError:
            log = (job / (name + '-laws.log')).read_text()
            assert 'unsolved goals' in log and 'unknown identifier' not in log, log
        else:
            raise AssertionError(f'mutation survived: {name}')
        params = '[{ name := "x", ty := .uint256 }]' if kind == 'short-args' else '[]'
        functions = '[]' if kind == 'unknown' else '[fn]'
        value = '1' if kind == 'nonpayable' else '0'
        call = 'mutationInterpretWithInternals contract 0 tx' if route == 'helpers' else 'mutationInterpret contract tx'
        witness = f'''open Compiler Compiler.Proofs.IRGeneration
private def fn : IRFunction := {{ name := "probe", selector := 7, params := {params}, ret := .unit, body := [] }}
private def contract : IRContract := {{ name := "C", deploy := [], functions := {functions}, usesMapping := false }}
private def tx : IRTransaction := {{ sender := 0, msgValue := {value}, functionSelector := 7, args := [] }}
#reduce ({call} (IRState.initial 0)).revertData
'''
        expected = run(name + '-expected', definitions, witness)
        actual = run(name + '-actual', mutant, witness)
        replay = run(name + '-replay', mutant, witness)
        assert expected == ['some []'] and actual == ['none'] and actual == replay, (expected, actual, replay)
        rows.append(dict(name=name, expected=expected, actual=actual, replay=replay))
        print(name, 'compiled, detected by quantified laws, and independently replayed', flush=True)
    artifacts = {str(p.relative_to(job)): hashlib.sha256(p.read_bytes()).hexdigest()
                 for p in job.glob('*.lean')}
    assert unchanged()
    (job / 'success.json').write_text(json.dumps(dict(exit=0, sources_unchanged=True,
        identity=identity, artifacts=artifacts, rows=rows), indent=2))


if __name__ == '__main__':
    main()
