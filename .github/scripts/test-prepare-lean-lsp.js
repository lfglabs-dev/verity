'use strict';

const assert = require('assert');
const crypto = require('crypto');
const fs = require('fs');
const os = require('os');
const path = require('path');
const { spawnSync } = require('child_process');

const script = path.join(__dirname, 'prepare-lean-lsp.sh');

function writeRepo(root, toolchain) {
  const repo = path.join(root, 'repo');
  fs.mkdirSync(repo);
  fs.writeFileSync(path.join(repo, 'lean-toolchain'), toolchain);
  return repo;
}

function createFakeElanArchive(root) {
  const stage = path.join(root, 'archive-stage');
  const archive = path.join(root, 'elan-test.tar.gz');
  fs.mkdirSync(stage);
  fs.writeFileSync(path.join(stage, 'elan-init'), `#!/usr/bin/env bash
set -euo pipefail
printf '%s\\n' "$*" >> "$ELAN_INIT_LOG"
mkdir -p "$ELAN_HOME/bin"
cat > "$ELAN_HOME/bin/elan" <<'EOS'
#!/usr/bin/env bash
printf '%s\\n' "$*" >> "$ELAN_FAKE_LOG"
EOS
chmod +x "$ELAN_HOME/bin/elan"
`);
  fs.chmodSync(path.join(stage, 'elan-init'), 0o755);
  const tar = spawnSync('tar', ['-czf', archive, '-C', stage, 'elan-init'], { encoding: 'utf8' });
  assert.strictEqual(tar.status, 0, tar.stderr);
  const sha256 = crypto.createHash('sha256').update(fs.readFileSync(archive)).digest('hex');
  return { archive, sha256 };
}

function run(toolchain) {
  const root = fs.mkdtempSync(path.join(os.tmpdir(), 'ocr-lean-lsp-'));
  const repo = writeRepo(root, toolchain);
  const bin = path.join(root, 'bin');
  const elanLog = path.join(root, 'elan.log');
  const elanHome = path.join(root, 'elan');
  const envFile = path.join(root, 'github-env');
  const pathFile = path.join(root, 'github-path');
  fs.mkdirSync(bin);
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
  const root = fs.mkdtempSync(path.join(os.tmpdir(), 'ocr-lean-lsp-bootstrap-'));
  const repo = writeRepo(root, 'leanprover/lean4:v4.24.0\n');
  const elanHome = path.join(root, 'elan');
  const envFile = path.join(root, 'github-env');
  const pathFile = path.join(root, 'github-path');
  const initLog = path.join(root, 'elan-init.log');
  const elanLog = path.join(root, 'elan.log');
  const { archive, sha256 } = createFakeElanArchive(root);
  const result = spawnSync('bash', [script, repo], {
    encoding: 'utf8',
    env: {
      ...process.env,
      ELAN_HOME: elanHome,
      GITHUB_ENV: envFile,
      GITHUB_PATH: pathFile,
      ELAN_INIT_LOG: initLog,
      ELAN_FAKE_LOG: elanLog,
      PREPARE_LEAN_LSP_TESTING: '1',
      PREPARE_LEAN_LSP_TEST_ELAN_ARCHIVE: path.basename(archive),
      PREPARE_LEAN_LSP_TEST_ELAN_SHA256: sha256,
      PREPARE_LEAN_LSP_TEST_ELAN_URL: `file://${archive}`,
    },
  });
  assert.strictEqual(result.status, 0, result.stderr);
  assert.strictEqual(fs.readFileSync(initLog, 'utf8'), '-y --no-modify-path --default-toolchain none\n');
  assert.strictEqual(fs.readFileSync(elanLog, 'utf8'), 'toolchain install leanprover/lean4:v4.24.0\nrun leanprover/lean4:v4.24.0 lean --version\n');
  assert.strictEqual(fs.readFileSync(envFile, 'utf8'), 'LEAN_TOOLCHAIN=leanprover/lean4:v4.24.0\n');
}

{
  const source = fs.readFileSync(script, 'utf8');
  assert.match(source, /elan_version='v4\.1\.2'/);
  assert.match(source, /elan_sha256='f81c2e48c1588d4612cd2c8851947898a45ac8d72748a07dff3a5694f1cf589b'/);
  assert.match(source, /elan_bin="\$ELAN_HOME\/bin\/elan"/);
  assert.match(source, /--connect-timeout 20 --max-time 120/);
  assert.match(source, /ELAN_HOME="\$ELAN_HOME" "\$tmpdir\/elan-init"/);
  assert.doesNotMatch(source, /command -v elan/);
}

console.log('Lean LSP setup tests passed');
