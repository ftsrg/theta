/**
 * File transformation handlers module
 * Provides handlers for transforming generated files (e.g., .dot to .svg)
 */

const fs = require('fs');
const fsp = fs.promises;
const path = require('path');
const { execFileAsync } = require('../utils/processUtils');
const config = require('../utils/config');

/**
 * Handles .dot file transformation to SVG
 * @param {string} dotFile - Path to .dot file
 * @param {string} dotRel - Relative path for output
 * @param {string} runDir - Working directory
 * @returns {Promise<{path: string, size: number, truncated: boolean, content: string, generated: true}|null>}
 */
async function handleDotFile(dotFile, dotRel, runDir) {
  const runExec = config.BENCHEXEC_BIN;
  
  if (!fs.existsSync(runExec)) {
    console.warn('[FileHandler] runexec not found, skipping dot transformation');
    return null;
  }
  
  const svgPath = path.join(runDir, 'output.files', 'out.svg');
  const svgRel = dotRel.replace(/\.dot$/, '.svg');
  
  console.log(`[FileHandler] Transforming ${dotRel} to SVG...`);
  
  try {
    const dotArgs = [
      '--read-only-dir', '/',
      '--hidden-dir', '/home',
      '--dir', runDir,
      '--overlay-dir', runDir,
      '--timelimit', '15',
      '--memlimit', '1024MB',
      '--',
      'dot', '-Tsvg', dotFile, '-o', 'out.svg'
    ];
    
    const dotResult = await execFileAsync(runExec, dotArgs, { cwd: runDir });
    
    if (dotResult.code !== 0) {
      console.error(`[FileHandler] Dot transformation failed with code ${dotResult.code}`);
      console.error('[FileHandler] stdout:', dotResult.stdout);
      console.error('[FileHandler] stderr:', dotResult.stderr);
      return null;
    }
    
    if (!fs.existsSync(svgPath)) {
      console.error('[FileHandler] Dot transformation completed but output file not found');
      return null;
    }
    
    const svgStat = await fsp.stat(svgPath).catch((err) => {
      console.error('[FileHandler] Failed to stat SVG file:', err.message);
      return null;
    });
    
    if (!svgStat || svgStat.size === 0) {
      console.warn('[FileHandler] SVG file is empty');
      return null;
    }
    
    const svgSize = svgStat.size;
    const svgSliceSize = Math.min(svgSize, config.MAX_FILE_SIZE);
    const svgBuf = await fsp.readFile(svgPath);
    const svgContent = svgBuf.slice(0, svgSliceSize).toString('utf8');
    
    console.log(`[FileHandler] Successfully generated SVG (${svgSize} bytes)`);
    
    return {
      path: svgRel,
      size: svgSize,
      truncated: svgSize > config.MAX_FILE_SIZE,
      content: svgContent,
      generated: true
    };
    
  } catch (err) {
    console.error('[FileHandler] Dot transformation error:', err.message);
    return null;
  }
}

/**
 * Handles witness file linting
 * @param {string} witnessFile - Path to witness file
 * @param {string} witnessName - Filename of witness
 * @param {string} srcFile - Path to source file
 * @param {string} runDir - Working directory
 * @param {string} baseRel - Base relative path
 * @returns {Promise<{path: string, size: number, truncated: boolean, content: string, generated: true}|null>}
 */
async function handleWitnessFile(witnessFile, witnessName, srcFile, runDir, baseRel) {
  const runExec = config.BENCHEXEC_BIN;
  const svWitnessesDir = config.SV_WITNESSES_DIR;
  
  if (!fs.existsSync(runExec)) {
    console.warn('[FileHandler] runexec not found, skipping witness linting');
    return null;
  }
  
  if (!fs.existsSync(svWitnessesDir)) {
    console.warn('[FileHandler] sv-witnesses directory not found, skipping witness linting');
    return null;
  }
  
  const linterScript = path.join(svWitnessesDir, 'linter', 'witnesslinter.py');
  
  if (!fs.existsSync(linterScript)) {
    console.warn('[FileHandler] witnesslinter.py not found, skipping witness linting');
    return null;
  }
  
  if (!fs.existsSync(srcFile)) {
    console.warn('[FileHandler] Source file not found, skipping witness linting');
    return null;
  }
  
  const lintOutputPath = path.join(runDir, 'output.log');
  const lintOutputRel = baseRel
    ? path.join(path.dirname(baseRel), `${witnessName}.lint.txt`)
    : `${witnessName}.lint.txt`;
  
  console.log(`[FileHandler] Linting witness file: ${witnessName}...`);
  
  try {
    const linterArgs = [
      '--read-only-dir', '/',
      '--hidden-dir', '/home',
      '--dir', runDir,
      '--full-access-dir', runDir,
      '--timelimit', '15',
      '--memlimit', '1024MB',
      '--read-only-dir', svWitnessesDir,
      '--',
      'python3', linterScript,
      '--witness', witnessFile,
      srcFile
    ];
    
    const lintResult = await execFileAsync(runExec, linterArgs, { cwd: runDir });
    
    console.log(`[FileHandler] Linter completed with code ${lintResult.code}`);
    
    if (!fs.existsSync(lintOutputPath)) {
      console.error('[FileHandler] Linter output file not found');
      return null;
    }
    
    const lintStat = await fsp.stat(lintOutputPath).catch((err) => {
      console.error('[FileHandler] Failed to stat linter output:', err.message);
      return null;
    });
    
    if (!lintStat || lintStat.size === 0) {
      console.warn('[FileHandler] Linter output is empty');
      return null;
    }
    
    const lintSize = lintStat.size;
    const lintSliceSize = Math.min(lintSize, config.MAX_FILE_SIZE);
    const lintBuf = await fsp.readFile(lintOutputPath);
    const lintContent = lintBuf.slice(0, lintSliceSize).toString('utf8');
    
    console.log(`[FileHandler] Successfully linted witness (${lintSize} bytes)`);
    
    return {
      path: lintOutputRel,
      size: lintSize,
      truncated: lintSize > config.MAX_FILE_SIZE,
      content: lintContent,
      generated: true
    };
    
  } catch (err) {
    console.error('[FileHandler] Witness linting error:', err.message);
    return null;
  }
}

/**
 * Applies all file handlers to a file entry
 * @param {object} entry - File entry with name
 * @param {string} fullPath - Full path to file
 * @param {string} relativePath - Relative path
 * @param {string} srcFile - Source file path
 * @param {string} runDir - Working directory
 * @param {string} baseRel - Base relative path
 * @returns {Promise<Array>} Array of generated file objects
 */
async function applyFileHandlers(entry, fullPath, relativePath, srcFile, runDir, baseRel) {
  const results = [];
  
  // Handler for .dot files
  if (entry.name.endsWith('.dot')) {
    const svgFile = await handleDotFile(fullPath, relativePath, runDir);
    if (svgFile) {
      results.push(svgFile);
    }
  }
  
  // Handler for witness files
  if (entry.name === 'witness.yml' || entry.name === 'witness.graphml') {
    const lintFile = await handleWitnessFile(fullPath, entry.name, srcFile, runDir, baseRel);
    if (lintFile) {
      results.push(lintFile);
    }
  }
  
  return results;
}

module.exports = {
  handleDotFile,
  handleWitnessFile,
  applyFileHandlers
};
