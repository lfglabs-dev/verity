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
  const envFile = path.join(root, 'github-env');
  fs.mkdirSync(repo);
  fs.mkdirSync(bin);
  fs.writeFileSync(path.join(repo, 'lean-toolchain'), toolchain);
  fs.writeFileSync(path.join(bin, 'elan'), `#!/usr/bin/env bash\nprintf '%s\\n' "$*" >> '${elanLog}'\n`);
  fs.chmodSync(path.join(bin, 'elan'), 0o755);
  const result = spawnSync('bash', [script, repo], {
    encoding: 'utf8',
    env: { ...process.env, PATH: `${bin}:${process.env.PATH}`, ELAN_HOME: path.join(root, 'elan'), GITHUB_ENV: envFile },
  });
  return { root, envFile, elanLog, result };
}

{
  const { envFile, elanLog, result } = run('leanprover/lean4:v4.24.0\n');
  assert.strictEqual(result.status, 0, result.stderr);
  assert.strictEqual(fs.readFileSync(envFile, 'utf8'), 'LEAN_TOOLCHAIN=leanprover/lean4:v4.24.0\n');
  assert.strictEqual(fs.readFileSync(elanLog, 'utf8'), 'toolchain install leanprover/lean4:v4.24.0\nrun leanprover/lean4:v4.24.0 lean --version\n');
}

{
  const { result } = run('leanprover/lean4:nightly\n');
  assert.notStrictEqual(result.status, 0);
  assert.match(result.stdout, /Refusing non-pinned/);
}

console.log('Lean LSP setup tests passed');
