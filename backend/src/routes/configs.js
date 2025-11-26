const express = require('express');
const fs = require('fs');
const path = require('path');
const router = express.Router();

const PRESETS_FILE = path.join(__dirname, '..', '..', 'config', 'cli-presets.json');

router.get('/', (req, res) => {
  try {
    if (!fs.existsSync(PRESETS_FILE)) {
      return res.json({ presets: [] });
    }
    const raw = fs.readFileSync(PRESETS_FILE, 'utf8');
    const obj = JSON.parse(raw);
    const presets = Array.isArray(obj.presets) ? obj.presets : [];
    res.json({ presets });
  } catch (e) {
    console.error('[Configs] Failed to read presets:', e.message);
    res.status(500).json({ error: 'failed to read presets' });
  }
});

module.exports = router;
