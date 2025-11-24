/**
 * Theta release retrieval module
 * Handles downloading and managing Theta releases from GitHub
 */

const fs = require('fs');
const fsp = fs.promises;
const path = require('path');
const config = require('../utils/config');
const { getDirectorySize } = require('../utils/fileUtils');

// Active retrieval controllers for cancellation
const activeRetrieval = new Map();

// Track last checked release to avoid duplicate downloads
let lastCheckedRelease = null;

/**
 * Checks for new releases and auto-retrieves latest xcfa jar
 */
async function checkAndRetrieveNewRelease() {
  try {
    console.log('[Auto-Retrieval] Checking for new releases...');
    
    const resp = await fetch(config.GITHUB_RELEASES_API, {
      headers: { 'Accept': 'application/vnd.github+json' }
    });
    
    if (!resp.ok) {
      console.error(`[Auto-Retrieval] GitHub API error ${resp.status}`);
      return;
    }
    
    const releases = await resp.json();
    
    if (!releases || releases.length === 0) {
      console.log('[Auto-Retrieval] No releases found');
      return;
    }
    
    const latestRelease = releases[0];
    const latestTag = latestRelease.tag_name || latestRelease.name;
    
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
      lastCheckedRelease = latestTag;
      return;
    }
    
    // Check if already downloaded
    const targetDir = path.join(config.THETA_CACHE_DIR, latestTag);
    const destFile = path.join(targetDir, xcfaAsset.name);
    
    if (fs.existsSync(destFile)) {
      console.log(`[Auto-Retrieval] Asset ${xcfaAsset.name} already exists`);
      lastCheckedRelease = latestTag;
      return;
    }
    
    if (activeRetrieval.has(latestTag)) {
      console.log(`[Auto-Retrieval] Retrieval already in progress for ${latestTag}`);
      return;
    }
    
    console.log(`[Auto-Retrieval] Downloading ${xcfaAsset.name} (${xcfaAsset.size} bytes)`);
    await downloadAsset(latestTag, xcfaAsset);
    
    lastCheckedRelease = latestTag;
    console.log(`[Auto-Retrieval] Successfully retrieved ${latestTag}`);
    
  } catch (err) {
    console.error(`[Auto-Retrieval] Error checking releases: ${err.message}`);
  }
}

/**
 * Downloads a release asset
 * @private
 */
async function downloadAsset(version, asset) {
  const targetDir = path.join(config.THETA_CACHE_DIR, version);
  await fsp.mkdir(targetDir, { recursive: true });
  
  const tmpName = `${version}_${asset.name}_${Date.now()}`;
  const tmpFile = path.join(config.THETA_TEMP_DIR, tmpName);
  const destFile = path.join(targetDir, asset.name);
  
  const controller = new AbortController();
  activeRetrieval.set(version, controller);
  
  try {
    const dlResp = await fetch(asset.browser_download_url, { signal: controller.signal });
    
    if (!dlResp.ok) {
      throw new Error(`HTTP ${dlResp.status}`);
    }
    
    const fileStream = fs.createWriteStream(tmpFile);
    const reader = dlResp.body.getReader();
    let received = 0;
    
    while (true) {
      const { done, value } = await reader.read();
      
      if (done) break;
      
      received += value.length;
      fileStream.write(value);
      
      if (controller.signal.aborted) {
        fileStream.close();
        fs.unlink(tmpFile, () => {});
        throw new Error('Download cancelled');
      }
    }
    
    fileStream.end();
    
    // Move to final location
    try {
      await fsp.rename(tmpFile, destFile);
    } catch (renameErr) {
      if (renameErr.code === 'EXDEV') {
        console.log('[Auto-Retrieval] Cross-device move, using copy');
        await fsp.copyFile(tmpFile, destFile);
        fs.unlink(tmpFile, () => {});
      } else {
        throw renameErr;
      }
    }
    
    console.log(`[Auto-Retrieval] Successfully downloaded ${asset.name}`);
    
  } catch (err) {
    console.error(`[Auto-Retrieval] Download failed: ${err.message}`);
    fs.unlink(tmpFile, () => {});
    throw err;
  } finally {
    activeRetrieval.delete(version);
  }
}

/**
 * Cleans up old versions if cache exceeds size limit
 */
async function cleanupCacheIfNeeded() {
  try {
    console.log('[Cleanup] Checking cache size...');
    
    const totalSize = await getDirectorySize(config.THETA_CACHE_DIR);
    const sizeGB = (totalSize / (1024 * 1024 * 1024)).toFixed(2);
    
    console.log(`[Cleanup] Current cache size: ${sizeGB} GB`);
    
    if (totalSize <= config.MAX_CACHE_SIZE) {
      console.log('[Cleanup] Cache size within limits, no cleanup needed');
      return;
    }
    
    console.log(`[Cleanup] Cache exceeds 5GB limit, cleaning up old versions...`);
    
    const entries = await fsp.readdir(config.THETA_CACHE_DIR).catch((err) => {
      console.error('[Cleanup] Failed to read cache directory:', err.message);
      return [];
    });
    
    const versions = [];
    
    for (const entry of entries) {
      const fullPath = path.join(config.THETA_CACHE_DIR, entry);
      const stat = await fsp.stat(fullPath).catch((err) => {
        console.warn(`[Cleanup] Failed to stat ${entry}:`, err.message);
        return null;
      });
      
      if (!stat || !stat.isDirectory()) {
        console.log(`[Cleanup] Skipping non-directory: ${entry}`);
        continue;
      }
      
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
    
    let currentSize = totalSize;
    let deletedCount = 0;
    
    for (const version of versions) {
      if (currentSize <= config.MAX_CACHE_SIZE) {
        break;
      }
      
      // Keep at least one version
      if (versions.length - deletedCount <= 1) {
        console.log('[Cleanup] Keeping at least one version');
        break;
      }
      
      const sizeMB = (version.size / (1024 * 1024)).toFixed(2);
      console.log(`[Cleanup] Deleting old version: ${version.name} (${sizeMB} MB)`);
      
      await fsp.rm(version.path, { recursive: true, force: true }).catch((err) => {
        console.error(`[Cleanup] Failed to delete ${version.name}:`, err.message);
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

/**
 * Performs periodic maintenance (check releases and cleanup)
 */
async function periodicMaintenance() {
  console.log('[Maintenance] Starting periodic maintenance...');
  await checkAndRetrieveNewRelease();
  await cleanupCacheIfNeeded();
  console.log('[Maintenance] Periodic maintenance complete');
}

/**
 * Gets active retrieval controller for a version
 * @param {string} version - Version identifier
 * @returns {AbortController|undefined}
 */
function getActiveRetrieval(version) {
  return activeRetrieval.get(version);
}

/**
 * Cancels an active retrieval
 * @param {string} version - Version to cancel
 * @returns {boolean} True if cancelled, false if not active
 */
function cancelRetrieval(version) {
  const ctrl = activeRetrieval.get(version);
  
  if (!ctrl) {
    console.warn(`[Retrieval] No active retrieval for version: ${version}`);
    return false;
  }
  
  ctrl.abort();
  console.log(`[Retrieval] Cancelled retrieval for version: ${version}`);
  return true;
}

/**
 * Checks if a version is currently being retrieved
 * @param {string} version - Version to check
 * @returns {boolean}
 */
function isRetrievalActive(version) {
  return activeRetrieval.has(version);
}

module.exports = {
  periodicMaintenance,
  getActiveRetrieval,
  cancelRetrieval,
  isRetrievalActive,
  checkAndRetrieveNewRelease,
  cleanupCacheIfNeeded
};
