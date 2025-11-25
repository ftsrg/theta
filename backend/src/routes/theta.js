/**
 * Theta management API routes
 * Handles version listing, release fetching, building, and retrieving
 */

const express = require('express');
const fs = require('fs');
const fsp = fs.promises;
const path = require('path');
const { expressBasicAuth } = require('../auth/authMiddleware');
const { validateCsrfToken } = require('../auth/csrfManager');
const { ensureThetaVersion } = require('../theta/versionManager');
const { cancelRetrieval, isRetrievalActive } = require('../theta/releaseManager');
const config = require('../utils/config');

const router = express.Router();

/**
 * GET /api/theta/versions
 * Lists locally cached Theta versions
 */
router.get('/versions', async (req, res) => {
  try {
    const entries = await fsp.readdir(config.THETA_CACHE_DIR).catch((err) => {
      console.error('[Theta] Failed to read cache directory:', err.message);
      return [];
    });
    
    const versions = [];
    
    for (const e of entries) {
      const full = path.join(config.THETA_CACHE_DIR, e);
      const stat = await fsp.stat(full).catch((err) => {
        console.warn(`[Theta] Failed to stat ${e}:`, err.message);
        return null;
      });
      
      if (stat && stat.isDirectory()) {
        const jarFiles = (await fsp.readdir(full).catch((err) => {
          console.warn(`[Theta] Failed to read ${e}:`, err.message);
          return [];
        })).filter(f => f.endsWith('.jar'));
        
        versions.push({ name: e, jars: jarFiles });
      } else {
        console.log(`[Theta] Skipping non-directory: ${e}`);
      }
    }
    
    console.log(`[Theta] Found ${versions.length} cached version(s)`);
    res.json({ versions: versions.reverse() });
    
  } catch (err) {
    console.error('[Theta] Error listing versions:', err.message);
    res.status(500).json({ error: String(err) });
  }
});

/**
 * GET /api/theta/releases
 * Lists releases (live from GitHub if authenticated, cached otherwise)
 */
router.get('/releases', async (req, res) => {
  try {
    const csrf = req.headers['x-csrf-token'];
    const isAuthenticated = validateCsrfToken(csrf);
    
    console.log(`[Releases] Authenticated: ${isAuthenticated} (${csrf ? 'token provided' : 'no token'})`);
    
    if (isAuthenticated) {
      // Fetch live data from GitHub API
      console.log('[Releases] Fetching from GitHub API...');
      
      const resp = await fetch(config.GITHUB_RELEASES_API, {
        headers: { 'Accept': 'application/vnd.github+json' }
      });
      
      if (!resp.ok) {
        console.error(`[Releases] GitHub API error ${resp.status}`);
        return res.status(resp.status).json({
          error: `GitHub API error ${resp.status} (${resp.statusText})`
        });
      }
      
      const data = await resp.json();
      const releases = [];
      
      for (const r of data) {
        const tag = r.tag_name || r.name || r.id;
        const assets = (r.assets || [])
          .filter(a => a.name && a.name.endsWith('.jar'))
          .map(a => ({
            name: a.name,
            size: a.size,
            downloadUrl: a.browser_download_url
          }));
        
        if (assets.length) {
          releases.push({ tag, assets });
        } else {
          console.log(`[Releases] Skipping release ${tag} (no jar assets)`);
        }
      }
      
      console.log(`[Releases] Retrieved ${releases.length} release(s) from GitHub`);
      res.json({ releases, source: 'github' });
      
    } else {
      // Return locally cached releases only
      console.log('[Releases] Returning cached releases...');
      
      const entries = await fsp.readdir(config.THETA_CACHE_DIR).catch((err) => {
        console.error('[Releases] Failed to read cache directory:', err.message);
        return [];
      });
      
      const releases = [];
      
      for (const e of entries) {
        const full = path.join(config.THETA_CACHE_DIR, e);
        const stat = await fsp.stat(full).catch((err) => {
          console.warn(`[Releases] Failed to stat ${e}:`, err.message);
          return null;
        });
        
        if (stat && stat.isDirectory()) {
          const jarFiles = await fsp.readdir(full).catch((err) => {
            console.warn(`[Releases] Failed to read ${e}:`, err.message);
            return [];
          });
          
          const assets = jarFiles
            .filter(f => f.endsWith('.jar'))
            .map(name => {
              const jarPath = path.join(full, name);
              const jarStat = fs.statSync(jarPath, { throwIfNoEntry: false });
              return {
                name,
                size: jarStat ? jarStat.size : 0
              };
            });
          
          if (assets.length) {
            releases.push({ tag: e, assets });
          } else {
            console.log(`[Releases] Skipping directory ${e} (no jar files)`);
          }
        } else {
          console.log(`[Releases] Skipping non-directory: ${e}`);
        }
      }
      
      console.log(`[Releases] Retrieved ${releases.length} cached release(s)`);
      res.json({ releases, source: 'cache' });
    }
    
  } catch (err) {
    console.error('[Releases] Error fetching releases:', err.message);
    res.status(500).json({ error: String(err) });
  }
});

/**
 * POST /api/theta/build
 * Builds a new Theta version (requires Basic Auth and CSRF)
 */
router.post('/build', expressBasicAuth, async (req, res) => {
  const version = String(req.body.version || '').trim();
  const repo = String(req.body.repo || '').trim() || config.THETA_REPO_URL_DEFAULT;
  
  if (!version) {
    console.error('[Theta] Build request missing version');
    return res.status(400).json({ error: 'version required' });
  }
  
  const csrf = req.headers['x-csrf-token'];
  if (!validateCsrfToken(csrf)) {
    console.error('[Theta] Build request with invalid CSRF token');
    return res.status(403).json({ error: 'invalid or missing csrf token' });
  }
  
  try {
    console.log(`[Theta] Building version ${version} from ${repo}`);
    const buildInfo = await ensureThetaVersion(version, repo);
    
    console.log(`[Theta] Build successful: ${buildInfo.version}`);
    res.json({ status: 'ok', version: buildInfo.version });
    
  } catch (err) {
    console.error('[Theta] Build error:', err.message);
    res.status(500).json({ error: String(err.message || err) });
  }
});

/**
 * POST /api/theta/retrieve/stream
 * Streaming retrieval of a jar asset (handled in verification routes)
 * Note: This is mounted separately to handle the complex streaming logic
 */

/**
 * POST /api/theta/retrieve/cancel
 * Cancels an active retrieval (requires Basic Auth)
 */
router.post('/retrieve/cancel', expressBasicAuth, (req, res) => {
  const version = String(req.body.version || '').trim();
  
  if (!version) {
    console.error('[Retrieval] Cancel request missing version');
    return res.status(400).json({ error: 'version required' });
  }
  
  if (!isRetrievalActive(version)) {
    console.warn(`[Retrieval] No active retrieval for ${version}`);
    return res.status(404).json({ error: 'no active retrieval' });
  }
  
  cancelRetrieval(version);
  console.log(`[Retrieval] Cancelled retrieval for ${version}`);
  
  res.json({ status: 'cancelling' });
});

module.exports = router;
