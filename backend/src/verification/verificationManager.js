/**
 * Verification execution module
 * Handles running verification tasks with file collection
 */

const fs = require('fs');
const fsp = fs.promises;
const path = require('path');
const { loadJSONSync } = require('../utils/fileUtils');
const { sanitizeArgs, expandInputPlaceholders, execFileAsync } = require('../utils/processUtils');
const { applyFileHandlers } = require('./fileHandlers');
const config = require('../utils/config');

/**
 * Collects generated files from a run directory
 * @param {string} runDir - Directory containing generated files
 * @param {string} srcFile - Path to source file (to exclude)
 * @returns {Promise<Array>} Array of file objects
 */
async function collectGeneratedFiles(runDir, srcFile) {
  const files = [];
  
  console.log(`[Verification] Collecting generated files from ${runDir}`);
  
  /**
   * Recursively walks directory tree
   * @private
   */
  async function walk(dir, baseRel) {
    try {
      const entries = await fsp.readdir(dir, { withFileTypes: true });
      
      for (const ent of entries) {
        const full = path.join(dir, ent.name);
        const rel = baseRel ? path.join(baseRel, ent.name) : ent.name;
        
        if (ent.isDirectory()) {
          await walk(full, rel);
        } else if (ent.isFile()) {
          // Skip source file
          if (full === srcFile) {
            continue;
          }
          
          const stat = await fsp.stat(full).catch((err) => {
            console.warn(`[Verification] Failed to stat ${rel}:`, err.message);
            return null;
          });
          
          if (!stat) {
            continue;
          }
          
          const size = stat.size;
          let content = '';
          let truncated = false;
          
          if (size > 0) {
            const sliceSize = Math.min(size, config.MAX_FILE_SIZE);
            const buf = await fsp.readFile(full);
            content = buf.slice(0, sliceSize).toString('utf8');
            truncated = size > config.MAX_FILE_SIZE;
            
            if (truncated) {
              console.warn(`[Verification] File ${rel} truncated (${size} bytes)`);
            }
          } else {
            console.log(`[Verification] Empty file: ${rel}`);
          }
          
          files.push({ path: rel, size, truncated, content });
          
          // Apply file handlers (e.g., .dot -> .svg)
          const handlerResults = await applyFileHandlers(ent, full, rel, srcFile, runDir, baseRel);
          files.push(...handlerResults);
          
        } else {
          console.warn(`[Verification] Skipping non-file/non-directory: ${rel}`);
        }
      }
    } catch (err) {
      console.error(`[Verification] Error walking directory ${dir}:`, err.message);
    }
  }
  
  await walk(runDir, '');
  
  console.log(`[Verification] Collected ${files.length} file(s)`);
  return files;
}

/**
 * Prepares verification arguments for theta-jar execution
 * @param {object} requestBody - Request body containing verification parameters
 * @param {string} srcFile - Path to source file
 * @returns {object} Prepared execution parameters
 */
function prepareVerificationArgs(requestBody, srcFile) {
  const { binaryName, args, thetaVersion, jarFile } = requestBody;
  
  const version = String(thetaVersion || '').trim();
  if (!version) {
    throw new Error('thetaVersion required for theta-jar');
  }
  
  const jar = String(jarFile || '').trim();
  if (!jar) {
    throw new Error('jarFile required');
  }
  
  const jarPath = path.join(config.THETA_CACHE_DIR, version, jar);
  const resolvedJar = path.resolve(jarPath);
  const cacheRoot = path.resolve(config.THETA_CACHE_DIR);
  
  // Security: ensure jar is within cache directory
  if (!resolvedJar.startsWith(cacheRoot + path.sep)) {
    console.error('[Verification] Invalid jar path attempt:', jarPath);
    throw new Error('invalid jar path');
  }
  
  if (!fs.existsSync(resolvedJar)) {
    console.error('[Verification] Jar not found:', resolvedJar);
    throw new Error('jar not found');
  }
  
  const safeArgs = sanitizeArgs(Array.isArray(args) ? args : []);
  const { expanded, used } = expandInputPlaceholders(safeArgs, srcFile);
  
  console.log(`[Verification] Prepared args for ${binaryName}, version=${version}, jar=${jar}`);
  console.log(`[Verification] Placeholder used: ${used}`);
  
  return {
    version,
    jar,
    resolvedJar,
    finalArgs: ['-jar', resolvedJar, ...expanded],
    placeholderUsed: used
  };
}

/**
 * Validates verification request
 * @param {object} requestBody - Request body to validate
 * @returns {object|null} Whitelist entry if valid, null otherwise
 */
function validateVerificationRequest(requestBody) {
  const { code, binaryName } = requestBody || {};
  
  if (!code || typeof code !== 'string') {
    console.error('[Verification] Invalid or missing code');
    throw new Error('code missing');
  }
  
  if (!binaryName) {
    console.error('[Verification] Missing binaryName');
    throw new Error('binaryName missing');
  }
  
  const whitelist = loadJSONSync(config.WHITELIST_FILE, { binaries: [] });
  const thetaJarEntry = whitelist.binaries.find(
    b => b.name === binaryName && b.type === 'theta-jar'
  );
  
  if (!thetaJarEntry) {
    console.error(`[Verification] Binary not whitelisted: ${binaryName}`);
    throw new Error('binary not whitelisted');
  }
  
  console.log(`[Verification] Request validated for binary: ${binaryName}`);
  return thetaJarEntry;
}

/**
 * Creates a temporary run directory
 * @returns {Promise<{runDir: string, srcFile: string}>}
 */
async function createRunDirectory() {
  const tmpRoot = path.join(__dirname, '..', '..', 'tmp');
  await fsp.mkdir(tmpRoot, { recursive: true });
  
  const runBase = `run-${Date.now()}-${Math.random().toString(36).slice(2, 8)}`;
  const runDir = path.join(tmpRoot, runBase);
  
  await fsp.mkdir(runDir, { recursive: true });
  
  const srcFile = path.join(runDir, 'input.c');
  
  console.log(`[Verification] Created run directory: ${runBase}`);
  
  return { runDir, srcFile };
}

/**
 * Schedules cleanup of run directory
 * @param {string} runDir - Directory to clean up
 * @param {number} delayMs - Delay before cleanup in milliseconds
 */
function scheduleCleanup(runDir, delayMs = 5000) {
  setTimeout(() => {
    fs.rm(runDir, { recursive: true, force: true }, (err) => {
      if (err) {
        console.error(`[Verification] Failed to cleanup ${runDir}:`, err.message);
      } else {
        console.log(`[Verification] Cleaned up ${runDir}`);
      }
    });
  }, delayMs);
}

/**
 * Executes verification for non-streaming mode
 * @param {string} resolvedJar - Path to jar file
 * @param {string[]} finalArgs - Arguments for execution
 * @param {string} runDir - Working directory
 * @returns {Promise<object>} Execution result
 */
async function executeVerification(resolvedJar, finalArgs, runDir) {
  console.log('[Verification] Executing verification...');
  
  try {
    const result = await execFileAsync('java', finalArgs, { cwd: runDir });
    console.log(`[Verification] Execution completed with code ${result.code}`);
    return result;
  } catch (err) {
    console.error('[Verification] Execution error:', err.message);
    throw err;
  }
}

module.exports = {
  collectGeneratedFiles,
  prepareVerificationArgs,
  validateVerificationRequest,
  createRunDirectory,
  scheduleCleanup,
  executeVerification
};
