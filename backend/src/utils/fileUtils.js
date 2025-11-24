/**
 * File system utilities module
 * Provides helper functions for file operations
 */

const fs = require('fs');
const fsp = fs.promises;

/**
 * Loads and parses a JSON file synchronously
 * @param {string} file - Path to the JSON file
 * @param {*} fallback - Fallback value if file cannot be read or parsed
 * @returns {*} Parsed JSON or fallback value
 */
function loadJSONSync(file, fallback) {
  try {
    return JSON.parse(fs.readFileSync(file, 'utf8'));
  } catch (err) {
    console.error(`[FileUtils] Failed to load JSON from ${file}:`, err.message);
    return fallback;
  }
}

/**
 * Recursively copies a directory and its contents
 * @param {string} src - Source directory path
 * @param {string} dst - Destination directory path
 */
async function copyDirRecursive(src, dst) {
  try {
    await fsp.mkdir(dst, { recursive: true });
    const entries = await fsp.readdir(src, { withFileTypes: true });
    
    for (const ent of entries) {
      const s = path.join(src, ent.name);
      const d = path.join(dst, ent.name);
      
      if (ent.isDirectory()) {
        await copyDirRecursive(s, d);
      } else if (ent.isFile()) {
        await fsp.copyFile(s, d);
      } else {
        console.warn(`[FileUtils] Skipping non-file/non-directory entry: ${s}`);
      }
    }
  } catch (err) {
    console.error(`[FileUtils] Failed to copy directory from ${src} to ${dst}:`, err.message);
    throw err;
  }
}

/**
 * Calculates the total size of a directory recursively
 * @param {string} dirPath - Path to the directory
 * @returns {Promise<number>} Total size in bytes
 */
async function getDirectorySize(dirPath) {
  let totalSize = 0;
  
  try {
    const entries = await fsp.readdir(dirPath, { withFileTypes: true });
    
    for (const entry of entries) {
      const fullPath = path.join(dirPath, entry.name);
      
      if (entry.isDirectory()) {
        totalSize += await getDirectorySize(fullPath);
      } else if (entry.isFile()) {
        const stat = await fsp.stat(fullPath).catch(() => {
          console.warn(`[FileUtils] Failed to stat file: ${fullPath}`);
          return { size: 0 };
        });
        totalSize += stat.size;
      } else {
        console.warn(`[FileUtils] Skipping non-file/non-directory entry: ${fullPath}`);
      }
    }
  } catch (err) {
    console.error(`[FileUtils] Error calculating directory size for ${dirPath}:`, err.message);
    // Return accumulated size even if there was an error
  }
  
  return totalSize;
}

const path = require('path');

module.exports = {
  loadJSONSync,
  copyDirRecursive,
  getDirectorySize
};
