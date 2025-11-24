const express = require('express');
const https = require('https');
const path = require('path');
const fs = require('fs');
const fsp = fs.promises;
const cors = require('cors');
const { execFile } = require('child_process');

// --- Config & Constants ----------------------------------------------------
const PORT = process.env.PORT || 5175;
const USE_HTTPS = process.env.USE_HTTPS !== 'false';
const CERT_FILE = process.env.CERT_FILE || path.join(__dirname, '..', 'certs', 'cert.pem');
const KEY_FILE = process.env.KEY_FILE || path.join(__dirname, '..', 'certs', 'key.pem');
const BASIC_AUTH_FILE = process.env.BASIC_AUTH_FILE || path.join(__dirname, '..', 'config', 'credentials.json');
const WHITELIST_FILE = path.join(__dirname, '..', 'config', 'whitelist.json');
const EXAMPLES_DIR = path.join(__dirname, '..', '..', 'examples');
const THETA_CACHE_DIR = process.env.THETA_CACHE_DIR || path.join(__dirname, '..', 'data', 'theta-cache');
const THETA_TEMP_DIR = path.join(__dirname, '..', 'data', 'theta-temp');
const THETA_REPO_URL_DEFAULT = 'https://github.com/ftsrg/theta.git';
const MAX_THETA_VERSIONS = parseInt(process.env.MAX_THETA_VERSIONS || '5', 10);
const EXEC_TIMEOUT_MS = parseInt(process.env.EXEC_TIMEOUT_MS || '30000', 10);
const MAX_BUFFER = 20 * 1024 * 1024; // 20MB output cap
const CSRF_TOKEN_TTL_MS = 30 * 60 * 1000; // 30 minutes
const GITHUB_RELEASES_API = 'https://api.github.com/repos/ftsrg/theta/releases';

// ensure cache and temp directories
fs.mkdirSync(THETA_CACHE_DIR, { recursive: true });
fs.mkdirSync(THETA_TEMP_DIR, { recursive: true });

// --- Utility ---------------------------------------------------------------
function loadJSONSync(file, fallback) {
  try { return JSON.parse(fs.readFileSync(file, 'utf8')); } catch { return fallback; }
}
function loadCredsSync() {
  const parsed = loadJSONSync(BASIC_AUTH_FILE, null);
  if (!parsed) return null;
  return { username: String(parsed.username || ''), password: String(parsed.password || '') };
}
function sanitizeArgs(args) {
  if (!Array.isArray(args)) return [];
  const safe = [];
  for (const a of args) {
    if (typeof a !== 'string') continue;
    if (a.length > 200) continue;
    safe.push(a);
  }
  return safe.slice(0, 50); // cap number of args
}

function expandInputPlaceholders(argList, srcFile) {
  const PLACEHOLDER = '%in';
  let used = false;
  const expanded = argList.map(a => {
    if (a === PLACEHOLDER) { used = true; return srcFile; }
    if (a.includes(PLACEHOLDER)) { used = true; return a.replaceAll(PLACEHOLDER, srcFile); }
    return a;
  });
  return { expanded, used };
}
function execFileAsync(file, args, opts = {}) {
  return new Promise((resolve) => {
    execFile(file, args, { timeout: EXEC_TIMEOUT_MS, maxBuffer: MAX_BUFFER, ...opts }, (err, stdout, stderr) => {
      const res = { stdout: stdout || '', stderr: stderr || '' };
      if (err) {
        res.code = err.code || 1;
        res.error = err.message || String(err);
      } else {
        res.code = 0;
      }
      resolve(res);
    });
  });
}

// --- Theta Version Manager -------------------------------------------------
const thetaBuildPromises = new Map(); // version -> promise
async function ensureThetaVersion(version, repoUrl) {
  if (!version || typeof version !== 'string' || version.length > 100) {
    throw new Error('Invalid Theta version');
  }
  if (thetaBuildPromises.has(version)) return thetaBuildPromises.get(version);
  const p = (async () => {
    const repo = repoUrl || THETA_REPO_URL_DEFAULT;
    const targetDir = path.join(THETA_CACHE_DIR, version);
    try {
      await fsp.mkdir(targetDir, { recursive: true });
      // If already built (theta-start.sh exists), return early
      const startScript = path.join(targetDir, 'theta-start.sh');
      if (fs.existsSync(startScript)) return { version, path: targetDir, startScript };

      // Clone (attempt branch/tag first; fallback to full clone then checkout)
      const gitArgsShallow = ['clone', '--depth', '1', '--branch', version, repo, targetDir];
      let clone = await execFileAsync('git', gitArgsShallow);
      if (clone.code !== 0) {
        // fallback: clone default and checkout commit/tag
        const fallbackDir = targetDir + '_tmp';
        await fsp.mkdir(fallbackDir, { recursive: true });
        let fullClone = await execFileAsync('git', ['clone', repo, fallbackDir]);
        if (fullClone.code !== 0) throw new Error(`Git clone failed: ${fullClone.stderr}`);
        const checkout = await execFileAsync('git', ['-C', fallbackDir, 'checkout', version]);
        if (checkout.code !== 0) throw new Error(`Git checkout failed: ${checkout.stderr}`);
        // move contents
        const entries = await fsp.readdir(fallbackDir);
        for (const e of entries) {
          await fsp.rename(path.join(fallbackDir, e), path.join(targetDir, e)).catch(async (err) => {
            if (err.code === 'EXDEV') {
              // fallback copy
              const src = path.join(fallbackDir, e);
              const dst = path.join(targetDir, e);
              const stat = await fsp.stat(src);
              if (stat.isDirectory()) {
                await copyDirRecursive(src, dst);
              } else {
                await fsp.copyFile(src, dst);
              }
            } else {
              throw err;
            }
          });
        }
        await fsp.rm(fallbackDir, { recursive: true, force: true });
      }

      // Patch JAVA_VERSION requirement if present (Theta script may require 17)
      const thetaStart = path.join(targetDir, 'theta-start.sh');
      if (fs.existsSync(thetaStart)) {
        let txt = await fsp.readFile(thetaStart, 'utf8');
        txt = txt.replace(/export JAVA_VERSION=17/g, 'export JAVA_VERSION=21');
        await fsp.writeFile(thetaStart, txt, 'utf8');
        await fsp.chmod(thetaStart, 0o755);
      }

      // Build using gradle wrapper if present; else, try gradle
      const gradlew = path.join(targetDir, 'gradlew');
      if (fs.existsSync(gradlew)) {
        await fsp.chmod(gradlew, 0o755);
        const build = await execFileAsync(gradlew, ['assemble'], { cwd: targetDir });
        if (build.code !== 0) throw new Error(`Theta build failed: ${build.stderr}`);
      } else {
        const build = await execFileAsync('gradle', ['assemble'], { cwd: targetDir });
        if (build.code !== 0) throw new Error(`Theta build failed (gradle): ${build.stderr}`);
      }

      await pruneThetaCache();
      return { version, path: targetDir, startScript: thetaStart };
    } catch (err) {
      // Cleanup target on failure
      await fsp.rm(path.join(THETA_CACHE_DIR, version), { recursive: true, force: true }).catch(()=>{});
      throw err;
    }
  })();
  thetaBuildPromises.set(version, p);
  try {
    const r = await p;
    return r;
  } finally {
    thetaBuildPromises.delete(version);
  }
}

async function pruneThetaCache() {
  const entries = await fsp.readdir(THETA_CACHE_DIR).catch(()=>[]);
  const versions = [];
  for (const e of entries) {
    const full = path.join(THETA_CACHE_DIR, e);
    const stat = await fsp.stat(full).catch(()=>null);
    if (!stat || !stat.isDirectory()) continue;
    versions.push({ name: e, mtime: stat.mtimeMs });
  }
  if (versions.length <= MAX_THETA_VERSIONS) return;
  versions.sort((a,b)=>a.mtime - b.mtime);
  const excess = versions.length - MAX_THETA_VERSIONS;
  for (let i=0;i<excess;i++) {
    const victim = path.join(THETA_CACHE_DIR, versions[i].name);
    await fsp.rm(victim, { recursive: true, force: true }).catch(()=>{});
  }
}

async function copyDirRecursive(src, dst) {
  await fsp.mkdir(dst, { recursive: true });
  const entries = await fsp.readdir(src, { withFileTypes: true });
  for (const ent of entries) {
    const s = path.join(src, ent.name);
    const d = path.join(dst, ent.name);
    if (ent.isDirectory()) await copyDirRecursive(s, d);
    else if (ent.isFile()) await fsp.copyFile(s, d);
  }
}

// --- Auth Middleware -------------------------------------------------------
function expressBasicAuth(req, res, next) {
  const creds = loadCredsSync();
  if (!creds || !creds.username) return unauthorized(res);
  const auth = req.headers['authorization'];
  if (!auth || !auth.startsWith('Basic ')) return unauthorized(res);
  const token = auth.slice('Basic '.length);
  let decoded;
  try {
    decoded = Buffer.from(token, 'base64').toString('utf8');
  } catch {
    return unauthorized(res);
  }
  const idx = decoded.indexOf(':');
  if (idx === -1) return unauthorized(res);
  const u = decoded.slice(0, idx);
  const p = decoded.slice(idx + 1);
  if (u === creds.username && p === creds.password) return next();
  return unauthorized(res);
}
function unauthorized(res) {
  res.setHeader('WWW-Authenticate', 'Basic realm="theta-ui"');
  return res.status(401).send('Unauthorized');
}

// --- CSRF Token Store -----------------------------------------------------
// Simple in-memory token store with expiry timestamps
const csrfTokens = new Map(); // token -> expiry
function generateCsrfToken() {
  return 'csrf_' + Math.random().toString(36).slice(2) + Math.random().toString(36).slice(2);
}
function issueCsrfToken() {
  const token = generateCsrfToken();
  csrfTokens.set(token, Date.now() + CSRF_TOKEN_TTL_MS);
  return token;
}
function validateCsrfToken(token) {
  if (!token) return false;
  const exp = csrfTokens.get(token);
  if (!exp) return false;
  if (Date.now() > exp) {
    csrfTokens.delete(token);
    return false;
  }
  return true;
}
function pruneCsrfTokens() {
  const now = Date.now();
  for (const [tok, exp] of csrfTokens.entries()) {
    if (exp < now) csrfTokens.delete(tok);
  }
}
setInterval(pruneCsrfTokens, 5 * 60 * 1000).unref();

// --- Express App -----------------------------------------------------------
const app = express();
app.use(cors());
app.use(express.json({ limit: '1mb' }));

// --- Examples Endpoints ----------------------------------------------------
app.get('/api/examples', async (req, res) => {
  try {
    const results = [];
    async function walk(dir, base) {
      const entries = await fsp.readdir(dir, { withFileTypes: true });
      for (const ent of entries) {
        const full = path.join(dir, ent.name);
        const rel = base ? path.join(base, ent.name) : ent.name;
        if (ent.isDirectory()) await walk(full, rel);
        else if (ent.isFile() && (ent.name.endsWith('.c') || ent.name.endsWith('.cpp'))) results.push(rel);
      }
    }
    await walk(EXAMPLES_DIR, '');
    res.json(results);
  } catch (err) {
    res.status(500).json({ error: String(err) });
  }
});

app.get('/api/examples/*', async (req, res) => {
  try {
    const rel = req.params[0] || '';
    const full = path.join(EXAMPLES_DIR, rel);
    const resolved = path.resolve(full);
    const root = path.resolve(EXAMPLES_DIR);
    if (!resolved.startsWith(root + path.sep) && resolved !== root) return res.status(400).json({ error: 'invalid path' });
    const stat = await fsp.stat(resolved);
    if (!stat.isFile()) return res.status(404).json({ error: 'not found' });
    const content = await fsp.readFile(resolved, 'utf8');
    res.json({ name: rel, content });
  } catch (err) {
    res.status(500).json({ error: String(err) });
  }
});

// --- Theta Version Management Endpoints -----------------------------------
// Obtain a CSRF token (requires valid Basic Auth)
app.post('/api/auth/csrf', expressBasicAuth, (req, res) => {
  try {
    const token = issueCsrfToken();
    res.json({ token, ttlMs: CSRF_TOKEN_TTL_MS });
  } catch (err) {
    res.status(500).json({ error: String(err) });
  }
});
// Simple credential validation endpoint (does NOT require CSRF)
app.post('/api/auth/validate', expressBasicAuth, (req, res) => {
  res.json({ ok: true });
});
app.get('/api/theta/versions', async (req, res) => {
  try {
    const entries = await fsp.readdir(THETA_CACHE_DIR).catch(()=>[]);
    const versions = [];
    for (const e of entries) {
      const full = path.join(THETA_CACHE_DIR, e);
      const stat = await fsp.stat(full).catch(()=>null);
      if (stat && stat.isDirectory()) {
        const jarFiles = (await fsp.readdir(full).catch(()=>[])).filter(f=>f.endsWith('.jar'));
        versions.push({ name: e, jars: jarFiles });
      }
    }
    res.json({ versions });
  } catch (err) {
    res.status(500).json({ error: String(err) });
  }
});

// List releases with jar assets metadata (tag + asset names)
// If authenticated (valid CSRF token), fetch live data from GitHub
// Otherwise, return locally cached releases only
app.get('/api/theta/releases', async (req, res) => {
  try {
    const csrf = req.headers['x-csrf-token'];
    const isAuthenticated = validateCsrfToken(csrf);
    console.log(`[Releases] Authenticated: ${isAuthenticated} (${csrf ? 'token provided' : 'no token'})`);
    if (isAuthenticated) {
      // Fetch live data from GitHub API
      const resp = await fetch(GITHUB_RELEASES_API, { headers: { 'Accept': 'application/vnd.github+json' } });
      if (!resp.ok) return res.status(resp.status).json({ error: `GitHub API error ${resp.status} (${resp.statusText})` });
      const data = await resp.json();
      const releases = [];
      for (const r of data) {
        const tag = r.tag_name || r.name || r.id;
        const assets = (r.assets || []).filter(a=>a.name && a.name.endsWith('.jar')).map(a=>({ name: a.name, size: a.size, downloadUrl: a.browser_download_url }));
        if (assets.length) releases.push({ tag, assets });
      }
      res.json({ releases, source: 'github' });
    } else {
      // Return locally cached releases only
      const entries = await fsp.readdir(THETA_CACHE_DIR).catch(()=>[]);
      const releases = [];
      for (const e of entries) {
        const full = path.join(THETA_CACHE_DIR, e);
        const stat = await fsp.stat(full).catch(()=>null);
        if (stat && stat.isDirectory()) {
          const jarFiles = await fsp.readdir(full).catch(()=>[]);
          const assets = jarFiles
            .filter(f=>f.endsWith('.jar'))
            .map(name => {
              const jarPath = path.join(full, name);
              const jarStat = fs.statSync(jarPath, { throwIfNoEntry: false });
              return { name, size: jarStat ? jarStat.size : 0 };
            });
          if (assets.length) releases.push({ tag: e, assets });
        }
      }
      res.json({ releases, source: 'cache' });
    }
  } catch (err) {
    res.status(500).json({ error: String(err) });
  }
});

// Protected: building new Theta versions requires Basic Auth
app.post('/api/theta/build', expressBasicAuth, async (req, res) => {
  const version = String(req.body.version || '').trim();
  const repo = String(req.body.repo || '').trim() || THETA_REPO_URL_DEFAULT;
  if (!version) return res.status(400).json({ error: 'version required' });
  const csrf = req.headers['x-csrf-token'];
  if (!validateCsrfToken(csrf)) return res.status(403).json({ error: 'invalid or missing csrf token' });
  try {
    const buildInfo = await ensureThetaVersion(version, repo);
    res.json({ status: 'ok', version: buildInfo.version });
  } catch (err) {
    res.status(500).json({ error: String(err.message || err) });
  }
});

// Active retrieval controllers for cancellation: version -> AbortController
const activeRetrieval = new Map();

// Track last checked release to avoid duplicate downloads
let lastCheckedRelease = null;

// Periodic release checker - runs every 10 minutes
async function checkAndRetrieveNewRelease() {
  try {
    console.log('[Auto-Retrieval] Checking for new releases...');
    const resp = await fetch(GITHUB_RELEASES_API, { headers: { 'Accept': 'application/vnd.github+json' } });
    if (!resp.ok) {
      console.error(`[Auto-Retrieval] GitHub API error ${resp.status}`);
      return;
    }
    const releases = await resp.json();
    if (!releases || releases.length === 0) {
      console.log('[Auto-Retrieval] No releases found');
      return;
    }
    
    // Get the latest release
    const latestRelease = releases[0];
    const latestTag = latestRelease.tag_name || latestRelease.name;
    
    // Check if this is a new release
    if (lastCheckedRelease === latestTag) {
      console.log(`[Auto-Retrieval] Latest release ${latestTag} already retrieved`);
      return;
    }
    
    console.log(`[Auto-Retrieval] New release detected: ${latestTag}`);
    
    // Find xcfa jar asset
    const xcfaAsset = (latestRelease.assets || []).find(a => 
      a.name && a.name.endsWith('.jar') && a.name.includes('xcfa')
    );
    
    if (!xcfaAsset) {
      console.log(`[Auto-Retrieval] No xcfa jar found in release ${latestTag}`);
      lastCheckedRelease = latestTag; // Mark as checked to avoid repeated attempts
      return;
    }
    
    // Check if already downloaded
    const targetDir = path.join(THETA_CACHE_DIR, latestTag);
    const destFile = path.join(targetDir, xcfaAsset.name);
    if (fs.existsSync(destFile)) {
      console.log(`[Auto-Retrieval] Asset ${xcfaAsset.name} already exists`);
      lastCheckedRelease = latestTag;
      return;
    }
    
    // Prevent parallel retrieval
    if (activeRetrieval.has(latestTag)) {
      console.log(`[Auto-Retrieval] Retrieval already in progress for ${latestTag}`);
      return;
    }
    
    // Download the asset
    console.log(`[Auto-Retrieval] Downloading ${xcfaAsset.name} (${xcfaAsset.size} bytes)`);
    await fsp.mkdir(targetDir, { recursive: true });
    
    const tmpName = `${latestTag}_${xcfaAsset.name}_${Date.now()}`;
    const tmpFile = path.join(THETA_TEMP_DIR, tmpName);
    
    const controller = new AbortController();
    activeRetrieval.set(latestTag, controller);
    
    try {
      const dlResp = await fetch(xcfaAsset.browser_download_url, { signal: controller.signal });
      if (!dlResp.ok) {
        throw new Error(`HTTP ${dlResp.status}`);
      }
      
      const fileStream = fs.createWriteStream(tmpFile);
      let received = 0;
      const size = xcfaAsset.size || 0;
      const reader = dlResp.body.getReader();
      
      while (true) {
        const { done, value } = await reader.read();
        if (done) break;
        received += value.length;
        fileStream.write(value);
        
        if (controller.signal.aborted) {
          fileStream.close();
          fs.unlink(tmpFile, ()=>{});
          throw new Error('Download cancelled');
        }
      }
      
      fileStream.end();
      
      // Move to final location
      try {
        await fsp.rename(tmpFile, destFile);
      } catch (renameErr) {
        if (renameErr.code === 'EXDEV') {
          await fsp.copyFile(tmpFile, destFile);
          fs.unlink(tmpFile, ()=>{});
        } else {
          throw renameErr;
        }
      }
      
      console.log(`[Auto-Retrieval] Successfully downloaded ${xcfaAsset.name} for ${latestTag}`);
      lastCheckedRelease = latestTag;
    } catch (err) {
      console.error(`[Auto-Retrieval] Download failed: ${err.message}`);
      fs.unlink(tmpFile, ()=>{});
    } finally {
      activeRetrieval.delete(latestTag);
    }
  } catch (err) {
    console.error(`[Auto-Retrieval] Error checking releases: ${err.message}`);
  }
}

// Calculate directory size recursively
async function getDirectorySize(dirPath) {
  let totalSize = 0;
  try {
    const entries = await fsp.readdir(dirPath, { withFileTypes: true });
    for (const entry of entries) {
      const fullPath = path.join(dirPath, entry.name);
      if (entry.isDirectory()) {
        totalSize += await getDirectorySize(fullPath);
      } else if (entry.isFile()) {
        const stat = await fsp.stat(fullPath).catch(() => ({ size: 0 }));
        totalSize += stat.size;
      }
    }
  } catch (err) {
    // Ignore errors for missing/inaccessible directories
  }
  return totalSize;
}

// Cleanup old versions if cache exceeds size limit
async function cleanupCacheIfNeeded() {
  const MAX_CACHE_SIZE = 5 * 1024 * 1024 * 1024; // 5GB in bytes
  
  try {
    console.log('[Cleanup] Checking cache size...');
    const totalSize = await getDirectorySize(THETA_CACHE_DIR);
    const sizeGB = (totalSize / (1024 * 1024 * 1024)).toFixed(2);
    console.log(`[Cleanup] Current cache size: ${sizeGB} GB`);
    
    if (totalSize <= MAX_CACHE_SIZE) {
      console.log('[Cleanup] Cache size within limits, no cleanup needed');
      return;
    }
    
    console.log(`[Cleanup] Cache exceeds 5GB limit, cleaning up old versions...`);
    
    // Get all version directories with their sizes and mtimes
    const entries = await fsp.readdir(THETA_CACHE_DIR).catch(() => []);
    const versions = [];
    
    for (const entry of entries) {
      const fullPath = path.join(THETA_CACHE_DIR, entry);
      const stat = await fsp.stat(fullPath).catch(() => null);
      if (!stat || !stat.isDirectory()) continue;
      
      const size = await getDirectorySize(fullPath);
      versions.push({ 
        name: entry, 
        path: fullPath, 
        mtime: stat.mtimeMs,
        size: size
      });
    }
    
    if (versions.length === 0) {
      console.log('[Cleanup] No versions to clean up');
      return;
    }
    
    // Sort by modification time (oldest first)
    versions.sort((a, b) => a.mtime - b.mtime);
    
    // Delete oldest versions until we're under the limit
    let currentSize = totalSize;
    let deletedCount = 0;
    
    for (const version of versions) {
      if (currentSize <= MAX_CACHE_SIZE) break;
      
      // Keep at least the most recent version
      if (versions.length - deletedCount <= 1) {
        console.log('[Cleanup] Keeping at least one version');
        break;
      }
      
      console.log(`[Cleanup] Deleting old version: ${version.name} (${(version.size / (1024 * 1024)).toFixed(2)} MB)`);
      await fsp.rm(version.path, { recursive: true, force: true }).catch((err) => {
        console.error(`[Cleanup] Failed to delete ${version.name}: ${err.message}`);
      });
      
      currentSize -= version.size;
      deletedCount++;
    }
    
    const newSizeGB = (currentSize / (1024 * 1024 * 1024)).toFixed(2);
    console.log(`[Cleanup] Cleanup complete. Deleted ${deletedCount} version(s). New size: ${newSizeGB} GB`);
  } catch (err) {
    console.error(`[Cleanup] Error during cleanup: ${err.message}`);
  }
}

// Periodic maintenance task
async function periodicMaintenance() {
  await checkAndRetrieveNewRelease();
  await cleanupCacheIfNeeded();
}

// Start periodic checker (every 10 minutes)
const AUTO_RETRIEVAL_INTERVAL = 10 * 60 * 1000; // 10 minutes
setInterval(periodicMaintenance, AUTO_RETRIEVAL_INTERVAL);
// Run once at startup (after a short delay to let server initialize)
setTimeout(periodicMaintenance, 10000);

// Streaming retrieval of a single jar asset
app.post('/api/theta/retrieve/stream', expressBasicAuth, async (req, res) => {
  const version = String(req.body.version || '').trim();
  const assetName = String(req.body.assetName || '').trim();
  if (!version || !assetName) return res.status(400).json({ error: 'version and assetName required' });
  const csrf = req.headers['x-csrf-token'];
  if (!validateCsrfToken(csrf)) return res.status(403).json({ error: 'invalid or missing csrf token' });

  res.setHeader('Content-Type', 'text/plain; charset=utf-8');
  res.setHeader('Cache-Control', 'no-cache');
  res.setHeader('Transfer-Encoding', 'chunked');
  function send(line) { res.write(line.replace(/\r?\n/g,'')+'\n'); }
  function endOk() { send(`DONE: ${version}`); res.end(); }
  function endErr(msg) { send(`ERROR: ${msg}`); res.end(); }

  // Prevent parallel retrieval for same version
  if (activeRetrieval.has(version)) return endErr('retrieval already in progress');

  try {
    // Fetch releases and locate asset
    send(`Querying releases for ${version}`);
    const ghr = await fetch(GITHUB_RELEASES_API, { headers: { 'Accept': 'application/vnd.github+json' } });
    if (!ghr.ok) return endErr(`GitHub API error ${ghr.status}`);
    const rels = await ghr.json();
    const release = rels.find(r => (r.tag_name || r.name) === version);
    if (!release) return endErr('release not found');
    const asset = (release.assets||[]).find(a=>a.name === assetName);
    if (!asset) return endErr('asset not found');
    if (!asset.browser_download_url) return endErr('missing download url');
    const targetDir = path.join(THETA_CACHE_DIR, version);
    await fsp.mkdir(targetDir, { recursive: true });
    const destFile = path.join(targetDir, asset.name);
    if (fs.existsSync(destFile)) {
      send('Asset already present, skipping download');
      return endOk();
    }
    // Download to dedicated temp directory, then move atomically when complete
    const tmpName = `${version}_${asset.name}_${Date.now()}`;
    const tmpFile = path.join(THETA_TEMP_DIR, tmpName);
    send(`Downloading to temp: ${tmpName}`);
    const controller = new AbortController();
    activeRetrieval.set(version, controller);
    send(`Downloading ${asset.name} (${asset.size} bytes)`);
    const dlResp = await fetch(asset.browser_download_url, { signal: controller.signal });
    if (!dlResp.ok) {
      activeRetrieval.delete(version);
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
      } else if (received % (1024*128) < value.length) {
        send(`PROGRESS: ${received}/0`);
      }
      if (controller.signal.aborted) {
        fileStream.close();
        // Remove temp file from temp directory
        fs.unlink(tmpFile, ()=>{});
        activeRetrieval.delete(version);
        return endErr('cancelled');
      }
    }
    fileStream.end();
    activeRetrieval.delete(version);
    // Final progress line guarantee (100%) if size known and not already sent
    if (size > 0 && lastReportPct !== 100) {
      const elapsedMs = Date.now() - started;
      const speed = elapsedMs > 0 ? (received / 1024) / (elapsedMs / 1000) : 0;
      send(`PROGRESS 100% ${received}/${size} ${Math.round(speed)}KB/s ETA:0s`);
    }
    // Move from temp directory to final location atomically
    send(`Moving to final location: ${asset.name}`);
    try {
      await fsp.rename(tmpFile, destFile);
    } catch (renameErr) {
      if (renameErr.code === 'EXDEV') {
        // Fallback copy across devices
        await fsp.copyFile(tmpFile, destFile);
        fs.unlink(tmpFile, ()=>{});
      } else {
        // Failure: cleanup temp and report error
        fs.unlink(tmpFile, ()=>{});
        return endErr(`move failed: ${renameErr.message}`);
      }
    }
    send('Download complete');
    endOk();
  } catch (err) {
    activeRetrieval.delete(version);
    endErr(err.message || String(err));
  }
});

// Cancel retrieval
app.post('/api/theta/retrieve/cancel', expressBasicAuth, (req, res) => {
  const version = String(req.body.version || '').trim();
  if (!version) return res.status(400).json({ error: 'version required' });
  const ctrl = activeRetrieval.get(version);
  if (!ctrl) return res.status(404).json({ error: 'no active retrieval' });
  ctrl.abort();
  res.json({ status: 'cancelling' });
});

// helper to spawn and stream
function spawnAndStream(cmd, args, send, opts = {}) {
  return new Promise((resolve) => {
    const { spawn } = require('child_process');
    const child = spawn(cmd, args, { ...opts });
    let stderrBuf = '';
    child.stdout.on('data', d => splitLines(d).forEach(l=> l && send(`OUT: ${l}`)));
    child.stderr.on('data', d => { const lines = splitLines(d); lines.forEach(l=> l && send(`ERR: ${l}`)); stderrBuf += d.toString(); });
    child.on('error', e => { send(`ERR: spawn error ${e.message}`); resolve({ code: 1, stderr: stderrBuf }); });
    child.on('close', code => { send(`EXIT: ${cmd} ${code}`); resolve({ code, stderr: stderrBuf }); });
  });
}
function splitLines(buf) { return buf.toString().split(/\r?\n/); }

// --- Verification Endpoint -------------------------------------------------
// Active verify processes: runId -> child process
const activeVerify = new Map();
app.post('/api/verify', async (req, res) => {
  const { code, binaryName, args, thetaVersion, jarFile } = req.body || {};
  if (!code || typeof code !== 'string') return res.status(400).json({ error: 'code missing' });
  if (!binaryName) return res.status(400).json({ error: 'binaryName missing' });
  const whitelist = loadJSONSync(WHITELIST_FILE, { binaries: []});
  const thetaJarEntry = whitelist.binaries.find(b => b.name === binaryName && b.type === 'theta-jar');
  if (!thetaJarEntry) return res.status(400).json({ error: 'binary not whitelisted' });

  const safeArgs = sanitizeArgs(Array.isArray(args) ? args : []);
  console.log(`Verify request: binary=${binaryName}, thetaVersion=${thetaVersion || ''}, jarFile=${jarFile || ''}, args=[${safeArgs.join(', ')}]`);
  const tmpRoot = path.join(__dirname, '..', 'tmp');
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
    if (!version) return res.status(400).json({ error: 'thetaVersion required for theta-jar' });
    const jar = String(jarFile || '').trim();
    if (!jar) return res.status(400).json({ error: 'jarFile required' });
    const jarPath = path.join(THETA_CACHE_DIR, version, jar);
    const resolvedJar = path.resolve(jarPath);
    const cacheRoot = path.resolve(THETA_CACHE_DIR);
    if (!resolvedJar.startsWith(cacheRoot + path.sep)) return res.status(400).json({ error: 'invalid jar path' });
    if (!fs.existsSync(resolvedJar)) return res.status(404).json({ error: 'jar not found' });
    const { expanded, used } = expandInputPlaceholders(safeArgs, srcFile);
    const finalArgs = [resolvedJar, ...expanded];
    // java -jar <jar> [args with %in replaced or <source> [args]]
    result = await execFileAsync('java', ['-jar', ...finalArgs], { cwd: runDir });
    result.meta = { binary: 'theta-jar', version, jar: jar, args: finalArgs, placeholderUsed: used };
  } catch (err) {
    result = { code: 1, stdout: '', stderr: '', error: String(err.message || err), meta: { binary: binaryName } };
  } finally {
    // Cleanup source file after short delay (preserve runDir contents for immediate listing capture below)
    setTimeout(() => { fs.unlink(srcFile, ()=>{}); }, 2000);
  }
  result.meta = { ...(result.meta||{}), durationMs: Date.now() - start };

  // Collect generated files from runDir (excluding source file) up to 1MB each
  try {
    const files = [];
    const runExec = path.join(__dirname, '..', '..', 'benchexec', 'bin', 'runexec');
    const svWitnessesDir = path.join(__dirname, '..', '..', 'sv-witnesses');
    
    async function walk(dir, baseRel) {
      const entries = await fsp.readdir(dir, { withFileTypes: true });
      for (const ent of entries) {
        const full = path.join(dir, ent.name);
        const rel = baseRel ? path.join(baseRel, ent.name) : ent.name;
        if (ent.isDirectory()) {
          await walk(full, rel);
        } else if (ent.isFile()) {
          if (full === srcFile) continue; // skip source
          const stat = await fsp.stat(full).catch(()=>null);
          if (!stat) continue;
          const size = stat.size;
          const MAX_FILE = 1024 * 1024; // 1MB
          let content = '';
          let truncated = false;
            if (size > 0) {
              const sliceSize = Math.min(size, MAX_FILE);
              const buf = await fsp.readFile(full);
              content = buf.slice(0, sliceSize).toString('utf8');
              if (size > MAX_FILE) truncated = true;
            }
          files.push({ path: rel, size, truncated, content });
          
          // Special handlers for certain file types
          // Handler for .dot files - generate SVG
          if (ent.name.endsWith('.dot') && fs.existsSync(runExec)) {
            const svgPath = full.replace(/\.dot$/, '.svg');
            const svgRel = rel.replace(/\.dot$/, '.svg');
            try {
              const dotArgs = ['--dir', runDir, '--timelimit', '15', '--memlimit', '1024MB', '--', 'dot', '-Tsvg', full, '-o', svgPath];
              const dotResult = await execFileAsync(runExec, dotArgs, { cwd: runDir });
              if (dotResult.code === 0 && fs.existsSync(svgPath)) {
                const svgStat = await fsp.stat(svgPath).catch(()=>null);
                if (svgStat && svgStat.size > 0) {
                  const svgSize = svgStat.size;
                  const svgSliceSize = Math.min(svgSize, MAX_FILE);
                  const svgBuf = await fsp.readFile(svgPath);
                  const svgContent = svgBuf.slice(0, svgSliceSize).toString('utf8');
                  files.push({ path: svgRel, size: svgSize, truncated: svgSize > MAX_FILE, content: svgContent, generated: true });
                }
              }
            } catch (dotErr) {
              // Silently ignore dot transformation errors
            }
          }
          
          // Handler for witness files - run linter
          if ((ent.name === 'witness.yml' || ent.name === 'witness.graphml') && fs.existsSync(runExec) && fs.existsSync(svWitnessesDir)) {
            const linterScript = path.join(svWitnessesDir, 'linter', 'witnesslinter.py');
            if (fs.existsSync(linterScript) && fs.existsSync(srcFile)) {
              const lintOutputPath = path.join(runDir, `${ent.name}.lint.txt`);
              const lintOutputRel = baseRel ? path.join(path.dirname(baseRel), `${ent.name}.lint.txt`) : `${ent.name}.lint.txt`;
              try {
                const linterArgs = ['--dir', runDir, '--timelimit', '15', '--memlimit', '1024MB', '--read-only-dir', svWitnessesDir, '--', 'python3', linterScript, '--witness', full, srcFile];
                const lintResult = await execFileAsync(runExec, linterArgs, { cwd: runDir });
                // Collect linter output (stdout/stderr) regardless of exit code
                const lintContent = `Exit Code: ${lintResult.code}\n\n=== STDOUT ===\n${lintResult.stdout}\n\n=== STDERR ===\n${lintResult.stderr}`;
                await fsp.writeFile(lintOutputPath, lintContent, 'utf8');
                const lintSize = Buffer.byteLength(lintContent, 'utf8');
                files.push({ path: lintOutputRel, size: lintSize, truncated: false, content: lintContent, generated: true });
              } catch (lintErr) {
                // Silently ignore linter errors
              }
            }
          }
        }
      }
    }
    await walk(runDir, '');
    result.generatedFiles = files;
  } catch (genErr) {
    result.generatedFilesError = String(genErr.message || genErr);
  }
  // Schedule removal of runDir after short grace period
  setTimeout(() => { fs.rm(runDir, { recursive: true, force: true }, ()=>{}); }, 5000);
  res.json(result);
});

// Streaming verification endpoint
app.post('/api/verify/stream', async (req, res) => {
  const { code, binaryName, args, thetaVersion, jarFile } = req.body || {};
  if (!code || typeof code !== 'string') return res.status(400).json({ error: 'code missing' });
  if (!binaryName) return res.status(400).json({ error: 'binaryName missing' });
  const whitelist = loadJSONSync(WHITELIST_FILE, { binaries: [] });
  const thetaJarEntry = whitelist.binaries.find(b => b.name === binaryName && b.type === 'theta-jar');
  if (!thetaJarEntry) return res.status(400).json({ error: 'binary not whitelisted' });

  res.setHeader('Content-Type', 'text/plain; charset=utf-8');
  res.setHeader('Cache-Control', 'no-cache');
  res.setHeader('Transfer-Encoding', 'chunked');
  function send(line) { try { res.write((line || '').toString().replace(/\r?\n/g,'')+'\n'); } catch {} }
  function endErr(msg) { send(`ERROR: ${msg}`); try { res.end(); } catch {} }

  const safeArgs = sanitizeArgs(Array.isArray(args) ? args : []);
  const tmpRoot = path.join(__dirname, '..', 'tmp');
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
    const { spawn } = require('child_process');
    let child;
    if (thetaJarEntry) {
      const version = String(thetaVersion || '').trim();
      if (!version) return endErr('thetaVersion required for theta-jar');
      const jar = String(jarFile || '').trim();
      if (!jar) return endErr('jarFile required');
      const jarPath = path.join(THETA_CACHE_DIR, version, jar);
      const resolvedJar = path.resolve(jarPath);
      const cacheRoot = path.resolve(THETA_CACHE_DIR);
      if (!resolvedJar.startsWith(cacheRoot + path.sep)) return endErr('invalid jar path');
      if (!fs.existsSync(resolvedJar)) return endErr('jar not found');
      const { expanded, used } = expandInputPlaceholders(safeArgs, srcFile);
      const finalArgs = ['-jar', resolvedJar, ...expanded];
      meta = { binary: 'theta-jar', version, jar: jar, args: finalArgs, placeholderUsed: used };
      const libPath = path.join(__dirname, '..', '..', 'lib');
      const homeDir = path.join(process.env.HOME || '/home/' + process.env.USER, '.theta');
      await fsp.mkdir(homeDir, { recursive: true }).catch(()=>{});
      const env = { ...process.env, HOME: homeDir, LD_LIBRARY_PATH: libPath + (process.env.LD_LIBRARY_PATH ? ':' + process.env.LD_LIBRARY_PATH : '') };
      const runExec = path.join(__dirname, '..', '..', 'benchexec', 'bin', 'runexec');
      const backendRoot = path.join(__dirname, '..');
      const lib = path.join(__dirname, '..', '..', 'lib');
      const containerArgs = [
        '--dir', runDir,
        '--container',
        '--timelimit', '60',
        '--memlimit', '5120MB',
        '--read-only-dir', '/',
        '--hidden-dir', '/home',
        '--read-only-dir', backendRoot,
        '--read-only-dir', lib,
        '--full-access-dir', runDir,
        '--',
        'java', ...finalArgs
      ];
      child = spawn(runExec, containerArgs, { cwd: runDir, env });
    }
    if (!child) return endErr('spawn failed');

    activeVerify.set(runId, child);
    // Merge stdout and stderr to preserve order
    child.stdout.on('data', d => splitLines(d).forEach(l=> l && send(`OUT: ${l}`)));
    child.stderr.on('data', d => splitLines(d).forEach(l=> l && send(`ERR: ${l}`)));
    child.on('error', e => { send(`OUT: spawn error ${e.message}`); });
    child.on('close', code => { exitCode = typeof code === 'number' ? code : 1; activeVerify.delete(runId); });

    // If client disconnects, kill process
    req.on('close', () => {
      const ch = activeVerify.get(runId);
      if (ch) {
        try { ch.kill('SIGTERM'); } catch {}
        activeVerify.delete(runId);
      }
    });

    // Wait for child to finish
    await new Promise(resolve => child.on('close', resolve));
    const result = { code: exitCode, meta: { ...meta, durationMs: Date.now() - start } };

    // Collect generated files up to 1MB each
    try {
      const files = [];
      const runExec = path.join(__dirname, '..', '..', 'benchexec', 'bin', 'runexec');
      const svWitnessesDir = path.join(__dirname, '..', '..', 'sv-witnesses');
      
      async function walk(dir, baseRel) {
        const entries = await fsp.readdir(dir, { withFileTypes: true });
        for (const ent of entries) {
          const full = path.join(dir, ent.name);
          const rel = baseRel ? path.join(baseRel, ent.name) : ent.name;
          if (ent.isDirectory()) {
            await walk(full, rel);
          } else if (ent.isFile()) {
            if (full === srcFile) continue;
            const stat = await fsp.stat(full).catch(()=>null);
            if (!stat) continue;
            const size = stat.size;
            const MAX_FILE = 1024 * 1024;
            let content = '';
            let truncated = false;
            if (size > 0) {
              const sliceSize = Math.min(size, MAX_FILE);
              const buf = await fsp.readFile(full);
              content = buf.slice(0, sliceSize).toString('utf8');
              if (size > MAX_FILE) truncated = true;
            }
            files.push({ path: rel, size, truncated, content });
            
            // Special handlers for certain file types
            // Handler for .dot files - generate SVG
            if (ent.name.endsWith('.dot') && fs.existsSync(runExec)) {
              const svgPath = path.join(runDir, 'output.files', 'out.svg');
              const svgRel = rel.replace(/\.dot$/, '.svg');
              try {
                const dotArgs = ['--read-only-dir', '/', '--hidden-dir', '/home', '--dir', runDir, '--full-access-dir', runDir, '--timelimit', '15', '--memlimit', '1024MB', '--', 'dot', '-Tsvg', full, '-o', 'out.svg'];
                const dotResult = await execFileAsync(runExec, dotArgs, { cwd: runDir });
                if (dotResult.code === 0 && fs.existsSync(svgPath)) {
                  const svgStat = await fsp.stat(svgPath).catch(()=>null);
                  if (svgStat && svgStat.size > 0) {
                    const svgSize = svgStat.size;
                    const svgSliceSize = Math.min(svgSize, MAX_FILE);
                    const svgBuf = await fsp.readFile(svgPath);
                    const svgContent = svgBuf.slice(0, svgSliceSize).toString('utf8');
                    files.push({ path: svgRel, size: svgSize, truncated: svgSize > MAX_FILE, content: svgContent, generated: true });
                  }
                }
              } catch (dotErr) {
                // Silently ignore dot transformation errors
              }
            }
            
            // Handler for witness files - run linter
            if ((ent.name === 'witness.yml' || ent.name === 'witness.graphml') && fs.existsSync(runExec) && fs.existsSync(svWitnessesDir)) {
              const linterScript = path.join(svWitnessesDir, 'linter', 'witnesslinter.py');
              if (fs.existsSync(linterScript) && fs.existsSync(srcFile)) {
                const lintOutputRel = baseRel ? path.join(path.dirname(baseRel), `${ent.name}.lint.txt`) : `${ent.name}.lint.txt`;
                try {
                  const linterArgs = ['--read-only-dir', '/', '--hidden-dir', '/home', '--dir', runDir, '--full-access-dir', runDir, '--timelimit', '15', '--memlimit', '1024MB', '--read-only-dir', svWitnessesDir, '--', 'python3', linterScript, '--witness', full, srcFile];
                  const lintResult = await execFileAsync(runExec, linterArgs, { cwd: runDir });
                  // Collect linter output (stdout/stderr) regardless of exit code
                  const lintContent = `Exit Code: ${lintResult.code}\n\n=== STDOUT ===\n${lintResult.stdout}\n\n=== STDERR ===\n${lintResult.stderr}`;
                  files.push({ path: lintOutputRel, size: Buffer.byteLength(lintContent, 'utf8'), truncated: false, content: lintContent, generated: true });
                } catch (lintErr) {
                  // Silently ignore linter errors
                }
              }
            }
          }
        }
      }
      await walk(runDir, '');
      result.generatedFiles = files;
    } catch (genErr) {
      result.generatedFilesError = String(genErr.message || genErr);
    }
    setTimeout(() => { fs.rm(runDir, { recursive: true, force: true }, ()=>{}); }, 5000);
    send('RESULT: ' + JSON.stringify(result));
    try { res.end(); } catch {}
  } catch (err) {
    try { res.end(); } catch {}
  } finally {
    setTimeout(() => { fs.unlink(srcFile, ()=>{}); }, 2000);
  }
});

// Cancel verification by runId
app.post('/api/verify/cancel', (req, res) => {
  try {
    const runId = String(req.body.runId || '').trim();
    if (!runId) return res.status(400).json({ error: 'runId required' });
    const child = activeVerify.get(runId);
    if (!child) return res.status(404).json({ error: 'not found' });
    try { child.kill('SIGTERM'); } catch {}
    activeVerify.delete(runId);
    return res.json({ status: 'cancelling' });
  } catch (err) {
    return res.status(500).json({ error: String(err.message || err) });
  }
});

// --- Health ----------------------------------------------------------------
app.get('/api/health', (req,res)=>res.json({ status: 'ok' }));

// --- Start -----------------------------------------------------------------
if (USE_HTTPS) {
  // Check if certificates exist
  if (!fs.existsSync(CERT_FILE) || !fs.existsSync(KEY_FILE)) {
    console.error('ERROR: SSL certificates not found!');
    console.error(`Certificate: ${CERT_FILE}`);
    console.error(`Private Key: ${KEY_FILE}`);
    console.error('\nRun: ./scripts/generate-certs.sh to create self-signed certificates');
    console.error('Or set USE_HTTPS=false to use HTTP instead');
    process.exit(1);
  }

  const httpsOptions = {
    key: fs.readFileSync(KEY_FILE),
    cert: fs.readFileSync(CERT_FILE)
  };

  https.createServer(httpsOptions, app).listen(PORT, () => {
    console.log(`theta-ui backend listening on https://localhost:${PORT}`);
    console.log('Using HTTPS with self-signed certificates');
    console.log('Note: Browsers will show security warnings for self-signed certificates');
  });
} else {
  app.listen(PORT, () => {
    console.log(`theta-ui backend listening on http://localhost:${PORT}`);
    console.log('Using HTTP (set USE_HTTPS=true to enable HTTPS)');
  });
}
