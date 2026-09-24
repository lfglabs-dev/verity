'use strict';
const assert = require('assert');
const fs = require('fs');
const os = require('os');
const path = require('path');
const { reviewGroup } = require('./ocr-packet-review');
const root = fs.mkdtempSync(path.join(os.tmpdir(), 'ocr-packet-status-'));
const previousPath = process.env.PATH;
const previousTemp = process.env.RUNNER_TEMP;
try {
  process.env.PATH = `${root}${path.delimiter}${previousPath}`;
  process.env.RUNNER_TEMP = root;
  const group = {files:['Example.lean'],packet_ids:['pkt-1'],exclude:[]};
  for (const status of ['success', 'completed_with_errors', 'error', 'failed', undefined]) {
    fs.writeFileSync(path.join(root, 'ocr'), '#!/usr/bin/env node\nprocess.stdout.write(' + JSON.stringify(JSON.stringify({status, comments:[]})) + ');\n', {mode:0o755});
    const result = reviewGroup({diff_base:'base',head:'head'}, group, 'rules.json');
    assert.strictEqual(result.status, status === 'success' ? 'success' : 'error', `CLI exits 0 with ${status}`);
  }
} finally {
  process.env.PATH = previousPath;
  if(previousTemp === undefined) delete process.env.RUNNER_TEMP; else process.env.RUNNER_TEMP = previousTemp;
  fs.rmSync(root,{recursive:true,force:true});
}
console.log('OCR packet status tests passed');
