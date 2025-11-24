/**
 * Examples API routes
 * Handles listing and fetching example source files
 */

const express = require('express');
const fsp = require('fs').promises;
const path = require('path');
const config = require('../utils/config');

const router = express.Router();

/**
 * GET /api/examples
 * Lists all available example files
 */
router.get('/', async (req, res) => {
  try {
    const results = [];
    
    /**
     * Recursively walks examples directory
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
          } else if (ent.isFile() && (ent.name.endsWith('.c') || ent.name.endsWith('.cpp'))) {
            results.push(rel);
          } else {
            console.log(`[Examples] Skipping non-C/C++ file: ${rel}`);
          }
        }
      } catch (err) {
        console.error(`[Examples] Error walking ${dir}:`, err.message);
      }
    }
    
    await walk(config.EXAMPLES_DIR, '');
    
    console.log(`[Examples] Found ${results.length} example file(s)`);
    res.json(results);
    
  } catch (err) {
    console.error('[Examples] Error listing examples:', err.message);
    res.status(500).json({ error: String(err) });
  }
});

/**
 * GET /api/examples/*
 * Fetches content of a specific example file
 */
router.get('/*', async (req, res) => {
  try {
    const rel = req.params[0] || '';
    console.log(`[Examples] Fetching example: ${rel}`);
    
    const full = path.join(config.EXAMPLES_DIR, rel);
    const resolved = path.resolve(full);
    const root = path.resolve(config.EXAMPLES_DIR);
    
    // Security: prevent path traversal
    if (!resolved.startsWith(root + path.sep) && resolved !== root) {
      console.error(`[Examples] Path traversal attempt: ${rel}`);
      return res.status(400).json({ error: 'invalid path' });
    }
    
    const stat = await fsp.stat(resolved);
    
    if (!stat.isFile()) {
      console.error(`[Examples] Not a file: ${rel}`);
      return res.status(404).json({ error: 'not found' });
    }
    
    const content = await fsp.readFile(resolved, 'utf8');
    
    console.log(`[Examples] Successfully read ${rel} (${content.length} bytes)`);
    res.json({ name: rel, content });
    
  } catch (err) {
    console.error('[Examples] Error fetching example:', err.message);
    res.status(500).json({ error: String(err) });
  }
});

module.exports = router;
