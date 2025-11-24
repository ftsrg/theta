/**
 * Theta version management module
 * Handles building, caching, and managing different Theta versions
 */

const fs = require('fs');
const fsp = fs.promises;
const path = require('path');
const { execFileAsync } = require('../utils/processUtils');
const { copyDirRecursive } = require('../utils/fileUtils');
const config = require('../utils/config');

// Track ongoing build promises to prevent duplicate builds
const thetaBuildPromises = new Map();

/**
 * Ensures a specific Theta version is built and cached
 * @param {string} version - Version tag/branch to build
 * @param {string} repoUrl - Git repository URL (optional)
 * @returns {Promise<{version: string, path: string, startScript: string}>}
 */
async function ensureThetaVersion(version, repoUrl) {
  if (!version || typeof version !== 'string' || version.length > 100) {
    console.error('[ThetaVersion] Invalid version string:', version);
    throw new Error('Invalid Theta version');
  }
  
  // Return existing build promise if already building
  if (thetaBuildPromises.has(version)) {
    console.log(`[ThetaVersion] Build for ${version} already in progress, waiting...`);
    return thetaBuildPromises.get(version);
  }
  
  const buildPromise = buildThetaVersion(version, repoUrl);
  thetaBuildPromises.set(version, buildPromise);
  
  try {
    const result = await buildPromise;
    console.log(`[ThetaVersion] Successfully ensured version ${version}`);
    return result;
  } finally {
    thetaBuildPromises.delete(version);
  }
}

/**
 * Internal function to build a Theta version
 * @private
 */
async function buildThetaVersion(version, repoUrl) {
  const repo = repoUrl || config.THETA_REPO_URL_DEFAULT;
  const targetDir = path.join(config.THETA_CACHE_DIR, version);
  
  console.log(`[ThetaVersion] Building version ${version} from ${repo}`);
  
  try {
    await fsp.mkdir(targetDir, { recursive: true });
    
    // Check if already built
    const startScript = path.join(targetDir, 'theta-start.sh');
    if (fs.existsSync(startScript)) {
      console.log(`[ThetaVersion] Version ${version} already built`);
      return { version, path: targetDir, startScript };
    }
    
    // Clone repository
    await cloneRepository(version, repo, targetDir);
    
    // Patch Java version if needed
    await patchJavaVersion(targetDir);
    
    // Build with Gradle
    await buildWithGradle(targetDir);
    
    // Prune old versions if needed
    await pruneThetaCache();
    
    console.log(`[ThetaVersion] Successfully built version ${version}`);
    return { version, path: targetDir, startScript: path.join(targetDir, 'theta-start.sh') };
    
  } catch (err) {
    console.error(`[ThetaVersion] Failed to build version ${version}:`, err.message);
    // Cleanup on failure
    await fsp.rm(targetDir, { recursive: true, force: true }).catch((cleanupErr) => {
      console.error(`[ThetaVersion] Failed to cleanup ${targetDir}:`, cleanupErr.message);
    });
    throw err;
  }
}

/**
 * Clones the Theta repository at specified version
 * @private
 */
async function cloneRepository(version, repo, targetDir) {
  console.log(`[ThetaVersion] Cloning repository for version ${version}`);
  
  // Try shallow clone first
  const gitArgsShallow = ['clone', '--depth', '1', '--branch', version, repo, targetDir];
  let clone = await execFileAsync('git', gitArgsShallow);
  
  if (clone.code === 0) {
    console.log(`[ThetaVersion] Shallow clone successful for ${version}`);
    return;
  }
  
  console.log(`[ThetaVersion] Shallow clone failed, attempting full clone...`);
  
  // Fallback: full clone and checkout
  const fallbackDir = targetDir + '_tmp';
  await fsp.mkdir(fallbackDir, { recursive: true });
  
  let fullClone = await execFileAsync('git', ['clone', repo, fallbackDir]);
  if (fullClone.code !== 0) {
    console.error('[ThetaVersion] Full clone failed:', fullClone.stderr);
    throw new Error(`Git clone failed: ${fullClone.stderr}`);
  }
  
  const checkout = await execFileAsync('git', ['-C', fallbackDir, 'checkout', version]);
  if (checkout.code !== 0) {
    console.error('[ThetaVersion] Checkout failed:', checkout.stderr);
    throw new Error(`Git checkout failed: ${checkout.stderr}`);
  }
  
  // Move contents to target directory
  const entries = await fsp.readdir(fallbackDir);
  for (const e of entries) {
    await fsp.rename(path.join(fallbackDir, e), path.join(targetDir, e)).catch(async (err) => {
      if (err.code === 'EXDEV') {
        console.log(`[ThetaVersion] Cross-device rename, using copy for ${e}`);
        const src = path.join(fallbackDir, e);
        const dst = path.join(targetDir, e);
        const stat = await fsp.stat(src);
        
        if (stat.isDirectory()) {
          await copyDirRecursive(src, dst);
        } else {
          await fsp.copyFile(src, dst);
        }
      } else {
        console.error(`[ThetaVersion] Failed to move ${e}:`, err.message);
        throw err;
      }
    });
  }
  
  await fsp.rm(fallbackDir, { recursive: true, force: true });
  console.log(`[ThetaVersion] Full clone and checkout successful for ${version}`);
}

/**
 * Patches Java version requirement in theta-start.sh if needed
 * @private
 */
async function patchJavaVersion(targetDir) {
  const thetaStart = path.join(targetDir, 'theta-start.sh');
  
  if (!fs.existsSync(thetaStart)) {
    console.log('[ThetaVersion] No theta-start.sh found, skipping Java version patch');
    return;
  }
  
  try {
    let txt = await fsp.readFile(thetaStart, 'utf8');
    const original = txt;
    txt = txt.replace(/export JAVA_VERSION=17/g, 'export JAVA_VERSION=21');
    
    if (txt !== original) {
      await fsp.writeFile(thetaStart, txt, 'utf8');
      console.log('[ThetaVersion] Patched Java version from 17 to 21');
    } else {
      console.log('[ThetaVersion] No Java version patching needed');
    }
    
    await fsp.chmod(thetaStart, 0o755);
  } catch (err) {
    console.error('[ThetaVersion] Failed to patch Java version:', err.message);
    throw err;
  }
}

/**
 * Builds Theta using Gradle
 * @private
 */
async function buildWithGradle(targetDir) {
  console.log('[ThetaVersion] Building with Gradle...');
  
  const gradlew = path.join(targetDir, 'gradlew');
  
  if (fs.existsSync(gradlew)) {
    await fsp.chmod(gradlew, 0o755);
    const build = await execFileAsync(gradlew, ['assemble'], { cwd: targetDir });
    
    if (build.code !== 0) {
      console.error('[ThetaVersion] Gradle build failed:', build.stderr);
      throw new Error(`Theta build failed: ${build.stderr}`);
    }
    
    console.log('[ThetaVersion] Gradle wrapper build successful');
  } else {
    console.log('[ThetaVersion] No gradlew found, using system gradle');
    const build = await execFileAsync('gradle', ['assemble'], { cwd: targetDir });
    
    if (build.code !== 0) {
      console.error('[ThetaVersion] System gradle build failed:', build.stderr);
      throw new Error(`Theta build failed (gradle): ${build.stderr}`);
    }
    
    console.log('[ThetaVersion] System gradle build successful');
  }
}

/**
 * Removes oldest cached versions if exceeding MAX_THETA_VERSIONS
 */
async function pruneThetaCache() {
  console.log('[ThetaVersion] Checking if cache pruning is needed...');
  
  const entries = await fsp.readdir(config.THETA_CACHE_DIR).catch((err) => {
    console.error('[ThetaVersion] Failed to read cache directory:', err.message);
    return [];
  });
  
  const versions = [];
  
  for (const e of entries) {
    const full = path.join(config.THETA_CACHE_DIR, e);
    const stat = await fsp.stat(full).catch((err) => {
      console.warn(`[ThetaVersion] Failed to stat ${e}:`, err.message);
      return null;
    });
    
    if (!stat || !stat.isDirectory()) {
      console.log(`[ThetaVersion] Skipping non-directory: ${e}`);
      continue;
    }
    
    versions.push({ name: e, mtime: stat.mtimeMs });
  }
  
  if (versions.length <= config.MAX_THETA_VERSIONS) {
    console.log(`[ThetaVersion] Cache has ${versions.length} versions (limit: ${config.MAX_THETA_VERSIONS}), no pruning needed`);
    return;
  }
  
  versions.sort((a, b) => a.mtime - b.mtime);
  const excess = versions.length - config.MAX_THETA_VERSIONS;
  
  console.log(`[ThetaVersion] Pruning ${excess} old version(s)...`);
  
  for (let i = 0; i < excess; i++) {
    const victim = path.join(config.THETA_CACHE_DIR, versions[i].name);
    console.log(`[ThetaVersion] Removing old version: ${versions[i].name}`);
    
    await fsp.rm(victim, { recursive: true, force: true }).catch((err) => {
      console.error(`[ThetaVersion] Failed to remove ${versions[i].name}:`, err.message);
    });
  }
  
  console.log('[ThetaVersion] Cache pruning complete');
}

module.exports = {
  ensureThetaVersion,
  pruneThetaCache
};
