"""Pinned tools and serialized native launch for real Midnight source controls."""
import hashlib
import os
from pathlib import Path
import subprocess
import sys

ROOT=Path(__file__).resolve().parents[2]


def launch(args, fixture, entrypoint, *, namespace="MidnightSourceCaller",
           capture="check_native_midnight_source_capture.py"):
    output=args.output.resolve();output.mkdir(parents=True,exist_ok=False)
    foundry=args.foundry.resolve()
    expected={'anvil':'9797b1e9bcdf65c9d6193470c94c2ee76e5524af2985cfb5db7fc641ba216cfa',
              'cast':'9db0414588508e131bdb4aa4bf46c3dd5357482a2ae81c48ffeeb6801a4daa8d'}
    for name,digest in expected.items():
        assert hashlib.sha256((foundry/name).read_bytes()).hexdigest()==digest,name
    os.environ['PATH']=str(foundry)+':'+os.environ['PATH']
    subprocess.run([sys.executable,str(ROOT/'scripts'/capture),'--check'],check=True)
    lean=(str(Path(os.environ['LEAN_SYSROOT'])/'bin/lean')
          if os.environ.get('LAKE_OVERRIDE_LEAN')=='true' and os.environ.get('LEAN_SYSROOT') else 'lean')
    driver=output/'Native.lean'
    driver.write_text(f'import Contracts.SolidityImportSmoke.{fixture}\ndef main : IO Unit := {namespace}.{entrypoint}\n')
    run=subprocess.run(['lake','env',lean,
        '--load-dynlib=.lake/packages/evmyul/.lake/build/lib/libleanffi.so',
        '--load-dynlib=.lake/packages/evmyul/.lake/build/lib/lean/evmyul_EvmYul_FFI_ffi.so',
        '--run',str(driver)],cwd=ROOT,capture_output=True,text=True,timeout=180)
    native_log=output/'native.log';native_log.write_text(run.stdout+run.stderr)
    assert run.returncode==0 and not run.stderr,run
    return output,foundry,native_log,driver


def identity(paths):
    return {str(p.relative_to(ROOT)) if p.is_relative_to(ROOT) else str(p):
            hashlib.sha256(p.read_bytes()).hexdigest() for p in paths}
