/**
 * Process execution utilities module
 * Provides helper functions for spawning and managing child processes
 */

const { execFile } = require('child_process');
const config = require('./config');

/**
 * Executes a file with given arguments and returns output
 * @param {string} file - Path to the executable
 * @param {string[]} args - Arguments to pass
 * @param {object} opts - Additional options for execFile
 * @returns {Promise<{stdout: string, stderr: string, code: number, error?: string}>}
 */
function execFileAsync(file, args, opts = {}) {
  return new Promise((resolve) => {
    const options = {
      timeout: config.EXEC_TIMEOUT_MS,
      maxBuffer: config.MAX_BUFFER,
      ...opts
    };
    
    execFile(file, args, options, (err, stdout, stderr) => {
      const res = {
        stdout: stdout || '',
        stderr: stderr || ''
      };
      
      if (err) {
        res.code = err.code || 1;
        res.error = err.message || String(err);
        console.error(`[ProcessUtils] execFile failed for ${file}:`, err.message);
      } else {
        res.code = 0;
      }
      
      resolve(res);
    });
  });
}

/**
 * Sanitizes command-line arguments for security
 * @param {any[]} args - Arguments array to sanitize
 * @returns {string[]} Sanitized arguments
 */
function sanitizeArgs(args) {
  if (!Array.isArray(args)) {
    console.warn('[ProcessUtils] sanitizeArgs received non-array input');
    return [];
  }
  
  const safe = [];
  for (const a of args) {
    if (typeof a !== 'string') {
      console.warn(`[ProcessUtils] Skipping non-string argument: ${typeof a}`);
      continue;
    }
    if (a.length > 200) {
      console.warn(`[ProcessUtils] Skipping overly long argument (${a.length} chars)`);
      continue;
    }
    safe.push(a);
  }
  
  // Cap number of args
  if (safe.length > 50) {
    console.warn(`[ProcessUtils] Trimming argument list from ${safe.length} to 50`);
    return safe.slice(0, 50);
  }
  
  return safe;
}

/**
 * Expands placeholder patterns in argument list with actual file path
 * @param {string[]} argList - List of arguments that may contain placeholders
 * @param {string} srcFile - File path to replace placeholders with
 * @returns {{expanded: string[], used: boolean}} Expanded arguments and whether placeholder was used
 */
function expandInputPlaceholders(argList, srcFile) {
  const PLACEHOLDER = '%in';
  let used = false;
  
  const expanded = argList.map(a => {
    if (a === PLACEHOLDER) {
      used = true;
      return srcFile;
    }
    if (a.includes(PLACEHOLDER)) {
      used = true;
      return a.replaceAll(PLACEHOLDER, srcFile);
    }
    return a;
  });
  
  if (used) {
    console.log(`[ProcessUtils] Expanded placeholder in arguments with: ${srcFile}`);
  }
  
  return { expanded, used };
}

/**
 * Splits buffer into lines for streaming output
 * @param {Buffer} buf - Buffer to split
 * @returns {string[]} Array of lines
 */
function splitLines(buf) {
  return buf.toString().split(/\r?\n/);
}

module.exports = {
  execFileAsync,
  sanitizeArgs,
  expandInputPlaceholders,
  splitLines
};
