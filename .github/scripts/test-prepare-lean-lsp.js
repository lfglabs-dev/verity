'use strict';

const assert = require('assert');
const fs = require('fs');
const os = require('os');
const path = require('path');
const { spawnSync } = require('child_process');

const script = path.join(__dirname, 'prepare-lean-lsp.sh');

function run(toolchain) {
  const root = fs.mkdtempSync(path.join(os.tmpdir(), 'ocr-lean-lsp-'));
  const repo = path.join(root, 'repo');
  const bin = path.join(root, 'bin');
  const elanLog = path.join(root, 'elan.log');
  const elanHome = path.join(root, 'elan');
  const envFile = path.join(root, 'github-env');
  const pathFile = path.join(root, 'github-path');
  fs.mkdirSync(repo);
  fs.mkdirSync(bin);
  fs.writeFileSync(path.join(repo, 'lean-toolchain'), toolchain);
  fs.mkdirSync(path.join(elanHome, 'bin'), { recursive: true });
  fs.writeFileSync(path.join(elanHome, 'bin', 'elan'), `#!/usr/bin/env bash\nprintf '%s\\n' "$*" >> '${elanLog}'\n`);
  fs.chmodSync(path.join(elanHome, 'bin', 'elan'), 0o755);
  const result = spawnSync('bash', [script, repo], {
    encoding: 'utf8',
    env: { ...process.env, PATH: `${bin}:${process.env.PATH}`, ELAN_HOME: elanHome, GITHUB_ENV: envFile, GITHUB_PATH: pathFile },
  });
  return { root, envFile, pathFile, elanLog, result };
}

{
  const { envFile, pathFile, elanLog, result } = run('leanprover/lean4:v4.24.0\n');
  assert.strictEqual(result.status, 0, result.stderr);
  assert.strictEqual(fs.readFileSync(envFile, 'utf8'), 'LEAN_TOOLCHAIN=leanprover/lean4:v4.24.0\n');
  assert.match(fs.readFileSync(pathFile, 'utf8'), /\/elan\/bin\n$/);
  assert.strictEqual(fs.readFileSync(elanLog, 'utf8'), 'toolchain install leanprover/lean4:v4.24.0\nrun leanprover/lean4:v4.24.0 lean --version\n');
}

{
  const { result } = run('leanprover/lean4:nightly\n');
  assert.notStrictEqual(result.status, 0);
  assert.match(result.stdout, /Refusing non-pinned/);
}

{
  const source = fs.readFileSync(script, 'utf8');
  assert.match(source, /elan_version='v4\.1\.2'/);
  assert.match(source, /elan_sha256='f81c2e48c1588d4612cd2c8851947898a45ac8d72748a07dff3a5694f1cf589b'/);
  assert.match(source, /elan_bin="\$ELAN_HOME\/bin\/elan"/);
  assert.match(source, /ELAN_HOME="\$ELAN_HOME" "\$tmpdir\/elan-init"/);
  assert.doesNotMatch(source, /command -v elan/);
}

console.log('Lean LSP setup tests passed');
