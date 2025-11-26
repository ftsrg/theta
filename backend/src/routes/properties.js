/**
 * Properties API routes
 * Handles listing and fetching property specification files
 */

const express = require('express');
const fsp = require('fs').promises;
const path = require('path');
const config = require('../utils/config');

const router = express.Router();

/**
 * GET /api/properties
 * Lists all available property files
 */
router.get('/', async (req, res) => {
  try {
    const results = [];
    
    /**
     * Recursively walks properties directory
     * @private
     */
    async function walk(dir, base) {
      try {
        const entries = await fsp.readdir(dir, { withFileTypes: true });
        
        for (const ent of entries) {
          const full = path.join(dir, ent.name);
          const rel = base ? path.join(base, ent.name) : ent.name;
          
          if (ent.isDirectory()) {
            await walk(full, rel);
          } else if (ent.isFile() && ent.name.endsWith('.prp')) {
            results.push(rel);
          } else {
            console.log(`[Properties] Skipping non-.prp file: ${rel}`);
          }
        }
      } catch (err) {
        console.error(`[Properties] Error walking ${dir}:`, err.message);
      }
    }
    
    await walk(config.PROPERTIES_DIR, '');
    
    console.log(`[Properties] Found ${results.length} property file(s)`);
    res.json(results);
    
  } catch (err) {
    console.error('[Properties] Error listing properties:', err.message);
    res.status(500).json({ error: String(err) });
  }
});

/**
 * GET /api/properties/*
 * Fetches content of a specific property file
 */
router.get('/*', async (req, res) => {
  try {
    const rel = req.params[0] || '';
    console.log(`[Properties] Fetching property: ${rel}`);
    
    const full = path.join(config.PROPERTIES_DIR, rel);
    const resolved = path.resolve(full);
    const root = path.resolve(config.PROPERTIES_DIR);
    
    // Security: prevent path traversal
    if (!resolved.startsWith(root + path.sep) && resolved !== root) {
      console.error(`[Properties] Path traversal attempt: ${rel}`);
      return res.status(400).json({ error: 'invalid path' });
    }
    
    const stat = await fsp.stat(resolved);
    
    if (!stat.isFile()) {
      console.error(`[Properties] Not a file: ${rel}`);
      return res.status(404).json({ error: 'not found' });
    }
    
    const content = await fsp.readFile(resolved, 'utf8');
    
    console.log(`[Properties] Successfully read ${rel} (${content.length} bytes)`);
    res.json({ name: rel, content });
    
  } catch (err) {
    console.error('[Properties] Error fetching property:', err.message);
    res.status(500).json({ error: String(err) });
  }
});

module.exports = router;
