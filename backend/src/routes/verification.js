/**
 * Verification API routes
 * Handles code verification, streaming execution, and release retrieval
 */

const express = require('express');
const fs = require('fs');
const fsp = fs.promises;
const path = require('path');
const { spawn } = require('child_process');
const { expressBasicAuth } = require('../auth/authMiddleware');
const { validateCsrfToken } = require('../auth/csrfManager');
const { loadJSONSync } = require('../utils/fileUtils');
const { sanitizeArgs, expandInputPlaceholders, execFileAsync, splitLines } = require('../utils/processUtils');
const config = require('../utils/config');
const { isRetrievalActive } = require('../theta/releaseManager');

const router = express.Router();

// Active verification processes: runId -> child process
const activeVerify = new Map();

// Active retrieval controllers for streaming
const activeRetrieval = new Map();

/**
 * POST /api/verify
 * Standard verification endpoint (non-streaming)
 */
router.post('/', async (req, res) => {
  const { code, binaryName, args, thetaVersion, jarFile } = req.body || {};
  
  // Validation
  if (!code || typeof code !== 'string') {
    console.error('[Verify] Missing or invalid code');
    return res.status(400).json({ error: 'code missing' });
  }
  
  if (!binaryName) {
    console.error('[Verify] Missing binaryName');
    return res.status(400).json({ error: 'binaryName missing' });
  }
  
  const whitelist = loadJSONSync(config.WHITELIST_FILE, { binaries: [] });
  const thetaJarEntry = whitelist.binaries.find(b => b.name === binaryName && b.type === 'theta-jar');
  
  if (!thetaJarEntry) {
    console.error(`[Verify] Binary not whitelisted: ${binaryName}`);
    return res.status(400).json({ error: 'binary not whitelisted' });
  }
  
  const safeArgs = sanitizeArgs(Array.isArray(args) ? args : []);
  console.log(`[Verify] Request: binary=${binaryName}, version=${thetaVersion || ''}, jar=${jarFile || ''}, args=[${safeArgs.join(', ')}]`);
  
  // Create run directory
  const tmpRoot = path.join(__dirname, '..', '..', 'tmp');
  await fsp.mkdir(tmpRoot, { recursive: true });
  const runBase = `run-${Date.now()}-${Math.random().toString(36).slice(2, 8)}`;
  const runDir = path.join(tmpRoot, runBase);
  await fsp.mkdir(runDir, { recursive: true });
  const srcFile = path.join(runDir, 'input.c');
  await fsp.writeFile(srcFile, code, 'utf8');
  
  const start = Date.now();
  let result;
  
  try {
    const version = String(thetaVersion || '').trim();
    if (!version) {
      console.error('[Verify] Missing thetaVersion');
      return res.status(400).json({ error: 'thetaVersion required for theta-jar' });
    }
    
    const jar = String(jarFile || '').trim();
    if (!jar) {
      console.error('[Verify] Missing jarFile');
      return res.status(400).json({ error: 'jarFile required' });
    }
    
    const jarPath = path.join(config.THETA_CACHE_DIR, version, jar);
    const resolvedJar = path.resolve(jarPath);
    const cacheRoot = path.resolve(config.THETA_CACHE_DIR);
    
    // Security check
    if (!resolvedJar.startsWith(cacheRoot + path.sep)) {
      console.error('[Verify] Invalid jar path attempt:', jarPath);
      return res.status(400).json({ error: 'invalid jar path' });
    }
    
    if (!fs.existsSync(resolvedJar)) {
      console.error('[Verify] Jar not found:', resolvedJar);
      return res.status(404).json({ error: 'jar not found' });
    }
    
    const { expanded, used } = expandInputPlaceholders(safeArgs, srcFile);
    const finalArgs = ['-jar', resolvedJar, ...expanded];
    
    console.log('[Verify] Executing verification...');
    result = await execFileAsync('java', finalArgs, { cwd: runDir });
    result.meta = { binary: 'theta-jar', version, jar, args: finalArgs, placeholderUsed: used };
    
  } catch (err) {
    console.error('[Verify] Execution error:', err.message);
    result = {
      code: 1,
      stdout: '',
      stderr: '',
      error: String(err.message || err),
      meta: { binary: binaryName }
    };
  } finally {
    // Cleanup source file after delay
    setTimeout(() => {
      fs.unlink(srcFile, (err) => {
        if (err) console.error('[Verify] Failed to unlink source file:', err.message);
      });
    }, 2000);
  }
  
  result.meta = { ...(result.meta || {}), durationMs: Date.now() - start };
  
  // Collect generated files
  try {
    const files = await collectGeneratedFiles(runDir, srcFile);
    result.generatedFiles = files;
  } catch (genErr) {
    console.error('[Verify] Error collecting files:', genErr.message);
    result.generatedFilesError = String(genErr.message || genErr);
  }
  
  // Schedule cleanup
  setTimeout(() => {
    fs.rm(runDir, { recursive: true, force: true }, (err) => {
      if (err) console.error('[Verify] Failed to cleanup run directory:', err.message);
      else console.log(`[Verify] Cleaned up ${runBase}`);
    });
  }, 5000);
  
  res.json(result);
});

/**
 * POST /api/verify/stream
 * Streaming verification endpoint with live output
 */
router.post('/stream', async (req, res) => {
  const { code, binaryName, args, thetaVersion, jarFile } = req.body || {};
  
  // Validation
  if (!code || typeof code !== 'string') {
    console.error('[VerifyStream] Missing or invalid code');
    return res.status(400).json({ error: 'code missing' });
  }
  
  if (!binaryName) {
    console.error('[VerifyStream] Missing binaryName');
    return res.status(400).json({ error: 'binaryName missing' });
  }
  
  const whitelist = loadJSONSync(config.WHITELIST_FILE, { binaries: [] });
  const thetaJarEntry = whitelist.binaries.find(b => b.name === binaryName && b.type === 'theta-jar');
  
  if (!thetaJarEntry) {
    console.error(`[VerifyStream] Binary not whitelisted: ${binaryName}`);
    return res.status(400).json({ error: 'binary not whitelisted' });
  }
  
  // Setup streaming response
  res.setHeader('Content-Type', 'text/plain; charset=utf-8');
  res.setHeader('Cache-Control', 'no-cache');
  res.setHeader('Transfer-Encoding', 'chunked');
  
  function send(line) {
    try {
      res.write((line || '').toString().replace(/\r?\n/g, '') + '\n');
    } catch (err) {
      console.error('[VerifyStream] Failed to write to response:', err.message);
    }
  }
  
  function endErr(msg) {
    send(`ERROR: ${msg}`);
    try {
      res.end();
    } catch (err) {
      console.error('[VerifyStream] Failed to end response:', err.message);
    }
  }
  
  const safeArgs = sanitizeArgs(Array.isArray(args) ? args : []);
  
  // Create run directory
  const tmpRoot = path.join(__dirname, '..', '..', 'tmp');
  await fsp.mkdir(tmpRoot, { recursive: true });
  const runBase = `run-${Date.now()}-${Math.random().toString(36).slice(2, 8)}`;
  const runDir = path.join(tmpRoot, runBase);
  await fsp.mkdir(runDir, { recursive: true });
  const srcFile = path.join(runDir, 'input.c');
  await fsp.writeFile(srcFile, code, 'utf8');
  
  const start = Date.now();
  
  try {
    let meta = {};
    let exitCode = 1;
    const runId = 'run_' + Math.random().toString(36).slice(2, 10);
    send(`RUN: ${runId}`);
    
    console.log(`[VerifyStream] Starting run ${runId}`);
    
    let child;
    
    if (thetaJarEntry) {
      const version = String(thetaVersion || '').trim();
      if (!version) {
        console.error('[VerifyStream] Missing thetaVersion');
        return endErr('thetaVersion required for theta-jar');
      }
      
      const jar = String(jarFile || '').trim();
      if (!jar) {
        console.error('[VerifyStream] Missing jarFile');
        return endErr('jarFile required');
      }
      
      const jarPath = path.join(config.THETA_CACHE_DIR, version, jar);
      const resolvedJar = path.resolve(jarPath);
      const cacheRoot = path.resolve(config.THETA_CACHE_DIR);
      
      if (!resolvedJar.startsWith(cacheRoot + path.sep)) {
        console.error('[VerifyStream] Invalid jar path attempt:', jarPath);
        return endErr('invalid jar path');
      }
      
      if (!fs.existsSync(resolvedJar)) {
        console.error('[VerifyStream] Jar not found:', resolvedJar);
        return endErr('jar not found');
      }
      
      const { expanded, used } = expandInputPlaceholders(safeArgs, srcFile);
      const finalArgs = ['-jar', resolvedJar, ...expanded];
      meta = { binary: 'theta-jar', version, jar, args: finalArgs, placeholderUsed: used };
      
      const libPath = config.LIB_DIR;
      const homeDir = path.join(process.env.HOME || '/home/' + process.env.USER, '.theta');
      await fsp.mkdir(homeDir, { recursive: true }).catch((err) => {
        console.error('[VerifyStream] Failed to create home directory:', err.message);
      });
      
      const env = {
        ...process.env,
        HOME: homeDir,
        LD_LIBRARY_PATH: libPath + (process.env.LD_LIBRARY_PATH ? ':' + process.env.LD_LIBRARY_PATH : '')
      };
      
      const runExec = config.BENCHEXEC_BIN;
      const backendRoot = config.BACKEND_ROOT;
      
      const containerArgs = [
        '--dir', runDir,
        '--container',
        '--timelimit', '60',
        '--memlimit', '5120MB',
        '--read-only-dir', '/',
        '--hidden-dir', '/home',
        '--read-only-dir', backendRoot,
        '--read-only-dir', libPath,
        '--full-access-dir', runDir,
        '--',
        'java', ...finalArgs
      ];
      
      console.log('[VerifyStream] Spawning verification process');
      child = spawn(runExec, containerArgs, { cwd: runDir, env });
    } else {
      console.error('[VerifyStream] Unsupported binary type');
      return endErr('unsupported binary type');
    }
    
    if (!child) {
      console.error('[VerifyStream] Failed to spawn process');
      return endErr('spawn failed');
    }
    
    activeVerify.set(runId, child);
    
    // Stream stdout and stderr
    child.stdout.on('data', d => splitLines(d).forEach(l => l && send(`OUT: ${l}`)));
    child.stderr.on('data', d => splitLines(d).forEach(l => l && send(`ERR: ${l}`)));
    child.on('error', e => {
      console.error('[VerifyStream] Process error:', e.message);
      send(`OUT: spawn error ${e.message}`);
    });
    child.on('close', code => {
      exitCode = typeof code === 'number' ? code : 1;
      activeVerify.delete(runId);
      console.log(`[VerifyStream] Process closed with code ${exitCode}`);
    });
    
    // Handle client disconnect
    req.on('close', () => {
      const ch = activeVerify.get(runId);
      if (ch) {
        console.log(`[VerifyStream] Client disconnected, killing process ${runId}`);
        try {
          ch.kill('SIGTERM');
        } catch (err) {
          console.error('[VerifyStream] Failed to kill process:', err.message);
        }
        activeVerify.delete(runId);
      }
    });
    
    // Wait for process to finish
    await new Promise(resolve => child.on('close', resolve));
    
    const result = { code: exitCode, meta: { ...meta, durationMs: Date.now() - start } };
    
    // Collect generated files
    try {
      const files = await collectGeneratedFilesStreaming(runDir, srcFile);
      result.generatedFiles = files;
    } catch (genErr) {
      console.error('[VerifyStream] Error collecting files:', genErr.message);
      result.generatedFilesError = String(genErr.message || genErr);
    }
    
    // Schedule cleanup
    setTimeout(() => {
      fs.rm(runDir, { recursive: true, force: true }, (err) => {
        if (err) console.error('[VerifyStream] Failed to cleanup:', err.message);
        else console.log(`[VerifyStream] Cleaned up ${runBase}`);
      });
    }, 5000);
    
    send('RESULT: ' + JSON.stringify(result));
    try {
      res.end();
    } catch (err) {
      console.error('[VerifyStream] Failed to end response:', err.message);
    }
    
  } catch (err) {
    console.error('[VerifyStream] Unexpected error:', err.message);
    try {
      res.end();
    } catch (endErr) {
      console.error('[VerifyStream] Failed to end response after error:', endErr.message);
    }
  } finally {
    setTimeout(() => {
      fs.unlink(srcFile, (err) => {
        if (err) console.error('[VerifyStream] Failed to unlink source:', err.message);
      });
    }, 2000);
  }
});

/**
 * POST /api/verify/cancel
 * Cancels an active verification by runId
 */
router.post('/cancel', (req, res) => {
  try {
    const runId = String(req.body.runId || '').trim();
    
    if (!runId) {
      console.error('[VerifyCancel] Missing runId');
      return res.status(400).json({ error: 'runId required' });
    }
    
    const child = activeVerify.get(runId);
    
    if (!child) {
      console.warn(`[VerifyCancel] No active verification for runId: ${runId}`);
      return res.status(404).json({ error: 'not found' });
    }
    
    try {
      child.kill('SIGTERM');
      console.log(`[VerifyCancel] Killed process ${runId}`);
    } catch (killErr) {
      console.error('[VerifyCancel] Failed to kill process:', killErr.message);
    }
    
    activeVerify.delete(runId);
    return res.json({ status: 'cancelling' });
    
  } catch (err) {
    console.error('[VerifyCancel] Error:', err.message);
    return res.status(500).json({ error: String(err.message || err) });
  }
});

/**
 * POST /api/theta/retrieve/stream
 * Streams retrieval of a jar asset from GitHub releases
 * Note: This is mounted here instead of theta routes due to shared streaming infrastructure
 */
const retrieveStreamRouter = express.Router();

retrieveStreamRouter.post('/theta/retrieve/stream', expressBasicAuth, async (req, res) => {
  const version = String(req.body.version || '').trim();
  const assetName = String(req.body.assetName || '').trim();
  
  if (!version || !assetName) {
    console.error('[RetrieveStream] Missing version or assetName');
    return res.status(400).json({ error: 'version and assetName required' });
  }
  
  const csrf = req.headers['x-csrf-token'];
  if (!validateCsrfToken(csrf)) {
    console.error('[RetrieveStream] Invalid CSRF token');
    return res.status(403).json({ error: 'invalid or missing csrf token' });
  }
  
  // Setup streaming response
  res.setHeader('Content-Type', 'text/plain; charset=utf-8');
  res.setHeader('Cache-Control', 'no-cache');
  res.setHeader('Transfer-Encoding', 'chunked');
  
  function send(line) {
    res.write(line.replace(/\r?\n/g, '') + '\n');
  }
  
  function endOk() {
    send(`DONE: ${version}`);
    res.end();
  }
  
  function endErr(msg) {
    send(`ERROR: ${msg}`);
    res.end();
  }
  
  // Prevent parallel retrieval for same version
  if (activeRetrieval.has(version)) {
    console.warn(`[RetrieveStream] Retrieval already in progress for ${version}`);
    return endErr('retrieval already in progress');
  }
  
  try {
    // Fetch releases and locate asset
    send(`Querying releases for ${version}`);
    console.log(`[RetrieveStream] Querying releases for ${version}`);
    
    const ghr = await fetch(config.GITHUB_RELEASES_API, {
      headers: { 'Accept': 'application/vnd.github+json' }
    });
    
    if (!ghr.ok) {
      console.error(`[RetrieveStream] GitHub API error ${ghr.status}`);
      return endErr(`GitHub API error ${ghr.status}`);
    }
    
    const rels = await ghr.json();
    const release = rels.find(r => (r.tag_name || r.name) === version);
    
    if (!release) {
      console.error(`[RetrieveStream] Release not found: ${version}`);
      return endErr('release not found');
    }
    
    const asset = (release.assets || []).find(a => a.name === assetName);
    
    if (!asset) {
      console.error(`[RetrieveStream] Asset not found: ${assetName}`);
      return endErr('asset not found');
    }
    
    if (!asset.browser_download_url) {
      console.error('[RetrieveStream] Missing download URL');
      return endErr('missing download url');
    }
    
    const targetDir = path.join(config.THETA_CACHE_DIR, version);
    await fsp.mkdir(targetDir, { recursive: true });
    const destFile = path.join(targetDir, asset.name);
    
    if (fs.existsSync(destFile)) {
      console.log(`[RetrieveStream] Asset already exists: ${assetName}`);
      send('Asset already present, skipping download');
      return endOk();
    }
    
    // Download to temp directory
    const tmpName = `${version}_${asset.name}_${Date.now()}`;
    const tmpFile = path.join(config.THETA_TEMP_DIR, tmpName);
    send(`Downloading to temp: ${tmpName}`);
    
    const controller = new AbortController();
    activeRetrieval.set(version, controller);
    
    send(`Downloading ${asset.name} (${asset.size} bytes)`);
    console.log(`[RetrieveStream] Downloading ${asset.name}`);
    
    const dlResp = await fetch(asset.browser_download_url, { signal: controller.signal });
    
    if (!dlResp.ok) {
      activeRetrieval.delete(version);
      console.error(`[RetrieveStream] Download HTTP error ${dlResp.status}`);
      return endErr(`download http ${dlResp.status}`);
    }
    
    const fileStream = fs.createWriteStream(tmpFile);
    let received = 0;
    const size = asset.size || 0;
    const started = Date.now();
    let lastReportPct = -1;
    const reader = dlResp.body.getReader();
    
    while (true) {
      const { done, value } = await reader.read();
      if (done) break;
      
      received += value.length;
      fileStream.write(value);
      
      if (size > 0) {
        const pct = Math.floor(received / size * 100);
        if (pct !== lastReportPct) {
          send(`PROGRESS: ${received}/${size}`);
          lastReportPct = pct;
        }
      } else if (received % (1024 * 128) < value.length) {
        send(`PROGRESS: ${received}/0`);
      }
      
      if (controller.signal.aborted) {
        fileStream.close();
        fs.unlink(tmpFile, () => {});
        activeRetrieval.delete(version);
        console.log(`[RetrieveStream] Download cancelled for ${version}`);
        return endErr('cancelled');
      }
    }
    
    fileStream.end();
    activeRetrieval.delete(version);
    
    // Final progress
    if (size > 0 && lastReportPct !== 100) {
      const elapsedMs = Date.now() - started;
      const speed = elapsedMs > 0 ? (received / 1024) / (elapsedMs / 1000) : 0;
      send(`PROGRESS 100% ${received}/${size} ${Math.round(speed)}KB/s ETA:0s`);
    }
    
    // Move to final location
    send(`Moving to final location: ${asset.name}`);
    try {
      await fsp.rename(tmpFile, destFile);
    } catch (renameErr) {
      if (renameErr.code === 'EXDEV') {
        console.log('[RetrieveStream] Cross-device move, using copy');
        await fsp.copyFile(tmpFile, destFile);
        fs.unlink(tmpFile, () => {});
      } else {
        console.error('[RetrieveStream] Move failed:', renameErr.message);
        fs.unlink(tmpFile, () => {});
        return endErr(`move failed: ${renameErr.message}`);
      }
    }
    
    send('Download complete');
    console.log(`[RetrieveStream] Successfully retrieved ${assetName} for ${version}`);
    endOk();
    
  } catch (err) {
    console.error('[RetrieveStream] Error:', err.message);
    activeRetrieval.delete(version);
    endErr(err.message || String(err));
  }
});

/**
 * Helper: Collects generated files (standard mode)
 * @private
 */
async function collectGeneratedFiles(runDir, srcFile) {
  const files = [];
  const runExec = config.BENCHEXEC_BIN;
  const svWitnessesDir = config.SV_WITNESSES_DIR;
  const MAX_FILE = config.MAX_FILE_SIZE;
  
  async function walk(dir, baseRel) {
    try {
      const entries = await fsp.readdir(dir, { withFileTypes: true });
      
      for (const ent of entries) {
        const full = path.join(dir, ent.name);
        const rel = baseRel ? path.join(baseRel, ent.name) : ent.name;
        
        if (ent.isDirectory()) {
          await walk(full, rel);
        } else if (ent.isFile()) {
          if (full === srcFile) continue;
          
          const stat = await fsp.stat(full).catch((err) => {
            console.warn('[CollectFiles] Failed to stat file:', err.message);
            return null;
          });
          
          if (!stat) continue;
          
          const size = stat.size;
          let content = '';
          let truncated = false;
          
          if (size > 0) {
            const sliceSize = Math.min(size, MAX_FILE);
            const buf = await fsp.readFile(full);
            content = buf.slice(0, sliceSize).toString('utf8');
            if (size > MAX_FILE) truncated = true;
          }
          
          files.push({ path: rel, size, truncated, content });
          
          // Handler for .dot files
          if (ent.name.endsWith('.dot') && fs.existsSync(runExec)) {
            const svgPath = full.replace(/\.dot$/, '.svg');
            const svgRel = rel.replace(/\.dot$/, '.svg');
            
            try {
              const dotArgs = ['--dir', runDir, '--timelimit', '15', '--memlimit', '1024MB', '--', 'dot', '-Tsvg', full, '-o', svgPath];
              const dotResult = await execFileAsync(runExec, dotArgs, { cwd: runDir });
              
              if (dotResult.code === 0 && fs.existsSync(svgPath)) {
                const svgStat = await fsp.stat(svgPath).catch(() => null);
                if (svgStat && svgStat.size > 0) {
                  const svgSize = svgStat.size;
                  const svgSliceSize = Math.min(svgSize, MAX_FILE);
                  const svgBuf = await fsp.readFile(svgPath);
                  const svgContent = svgBuf.slice(0, svgSliceSize).toString('utf8');
                  files.push({ path: svgRel, size: svgSize, truncated: svgSize > MAX_FILE, content: svgContent, generated: true });
                }
              }
            } catch (dotErr) {
              console.error('[CollectFiles] Dot transformation error:', dotErr.message);
            }
          }
          
          // Handler for witness files
          if ((ent.name === 'witness.yml' || ent.name === 'witness.graphml') && fs.existsSync(runExec) && fs.existsSync(svWitnessesDir)) {
            const linterScript = path.join(svWitnessesDir, 'linter', 'witnesslinter.py');
            if (fs.existsSync(linterScript) && fs.existsSync(srcFile)) {
              const lintOutputPath = path.join(runDir, `${ent.name}.lint.txt`);
              const lintOutputRel = baseRel ? path.join(path.dirname(baseRel), `${ent.name}.lint.txt`) : `${ent.name}.lint.txt`;
              
              try {
                const linterArgs = ['--dir', runDir, '--timelimit', '15', '--memlimit', '1024MB', '--read-only-dir', svWitnessesDir, '--', 'python3', linterScript, '--witness', full, srcFile];
                const lintResult = await execFileAsync(runExec, linterArgs, { cwd: runDir });
                const lintContent = `Exit Code: ${lintResult.code}\n\n=== STDOUT ===\n${lintResult.stdout}\n\n=== STDERR ===\n${lintResult.stderr}`;
                await fsp.writeFile(lintOutputPath, lintContent, 'utf8');
                const lintSize = Buffer.byteLength(lintContent, 'utf8');
                files.push({ path: lintOutputRel, size: lintSize, truncated: false, content: lintContent, generated: true });
              } catch (lintErr) {
                console.error('[CollectFiles] Linter error:', lintErr.message);
              }
            }
          }
        }
      }
    } catch (walkErr) {
      console.error('[CollectFiles] Error walking directory:', walkErr.message);
    }
  }
  
  await walk(runDir, '');
  return files;
}

/**
 * Helper: Collects generated files (streaming mode with different file paths)
 * @private
 */
async function collectGeneratedFilesStreaming(runDir, srcFile) {
  const files = [];
  const runExec = config.BENCHEXEC_BIN;
  const svWitnessesDir = config.SV_WITNESSES_DIR;
  const MAX_FILE = config.MAX_FILE_SIZE;
  
  async function walk(dir, baseRel) {
    try {
      const entries = await fsp.readdir(dir, { withFileTypes: true });
      
      for (const ent of entries) {
        const full = path.join(dir, ent.name);
        const rel = baseRel ? path.join(baseRel, ent.name) : ent.name;
        
        if (ent.isDirectory()) {
          await walk(full, rel);
        } else if (ent.isFile()) {
          if (full === srcFile) continue;
          
          const stat = await fsp.stat(full).catch((err) => {
            console.warn('[CollectFilesStream] Failed to stat:', err.message);
            return null;
          });
          
          if (!stat) continue;
          
          const size = stat.size;
          let content = '';
          let truncated = false;
          
          if (size > 0) {
            const sliceSize = Math.min(size, MAX_FILE);
            const buf = await fsp.readFile(full);
            content = buf.slice(0, sliceSize).toString('utf8');
            if (size > MAX_FILE) truncated = true;
          }
          
          files.push({ path: rel, size, truncated, content });
          
          // Handler for .dot files (different output path for streaming)
          if (ent.name.endsWith('.dot') && fs.existsSync(runExec)) {
            const svgPath = path.join(runDir, 'output.files', 'out.svg');
            const svgRel = rel.replace(/\.dot$/, '.svg');
            
            try {
              const dotArgs = ['--read-only-dir', '/', '--hidden-dir', '/home', '--dir', runDir, '--overlay-dir', runDir, '--timelimit', '15', '--memlimit', '1024MB', '--', 'dot', '-Tsvg', full, '-o', 'out.svg'];
              const dotResult = await execFileAsync(runExec, dotArgs, { cwd: runDir });
              
              if (dotResult.code === 0 && fs.existsSync(svgPath)) {
                const svgStat = await fsp.stat(svgPath).catch(() => null);
                if (svgStat && svgStat.size > 0) {
                  const svgSize = svgStat.size;
                  const svgSliceSize = Math.min(svgSize, MAX_FILE);
                  const svgBuf = await fsp.readFile(svgPath);
                  const svgContent = svgBuf.slice(0, svgSliceSize).toString('utf8');
                  files.push({ path: svgRel, size: svgSize, truncated: svgSize > MAX_FILE, content: svgContent, generated: true });
                }
              } else {
                console.error('[CollectFilesStream] Dot output not found, code:', dotResult.code);
              }
            } catch (dotErr) {
              console.error('[CollectFilesStream] Dot error:', dotErr.message);
            }
          }
          
          // Handler for witness files
          if ((ent.name === 'witness.yml' || ent.name === 'witness.graphml') && fs.existsSync(runExec) && fs.existsSync(svWitnessesDir)) {
            const linterScript = path.join(svWitnessesDir, 'linter', 'witnesslinter.py');
            if (fs.existsSync(linterScript) && fs.existsSync(srcFile)) {
              const lintOutputPath = path.join(runDir, 'output.log');
              const lintOutputRel = baseRel ? path.join(path.dirname(baseRel), `${ent.name}.lint.txt`) : `${ent.name}.lint.txt`;
              
              try {
                const linterArgs = ['--read-only-dir', '/', '--hidden-dir', '/home', '--dir', runDir, '--full-access-dir', runDir, '--timelimit', '15', '--memlimit', '1024MB', '--read-only-dir', svWitnessesDir, '--', 'python3', linterScript, '--witness', full, srcFile];
                const lintResult = await execFileAsync(runExec, linterArgs, { cwd: runDir });
                
                if (fs.existsSync(lintOutputPath)) {
                  const lintStat = await fsp.stat(lintOutputPath).catch(() => null);
                  if (lintStat && lintStat.size > 0) {
                    const lintSize = lintStat.size;
                    const lintSliceSize = Math.min(lintSize, MAX_FILE);
                    const lintBuf = await fsp.readFile(lintOutputPath);
                    const lintContent = lintBuf.slice(0, lintSliceSize).toString('utf8');
                    files.push({ path: lintOutputRel, size: lintSize, truncated: lintSize > MAX_FILE, content: lintContent, generated: true });
                  }
                } else {
                  console.error('[CollectFilesStream] Linter output not found');
                }
              } catch (lintErr) {
                console.error('[CollectFilesStream] Linter error:', lintErr.message);
              }
            }
          }
        }
      }
    } catch (walkErr) {
      console.error('[CollectFilesStream] Error walking directory:', walkErr.message);
    }
  }
  
  await walk(runDir, '');
  return files;
}

module.exports = router;
module.exports.retrieveStreamRouter = retrieveStreamRouter;
