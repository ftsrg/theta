const express = require('express');
const fs = require('fs');
const path = require('path');
const router = express.Router();

const CONFIG_FILE = path.join(__dirname, '..', '..', 'config', 'cli-presets.json');

router.get('/', (req, res) => {
  try {
    if (!fs.existsSync(CONFIG_FILE)) {
      return res.json({ modes: {} });
    }
    const raw = fs.readFileSync(CONFIG_FILE, 'utf8');
    const obj = JSON.parse(raw);
    const modes = obj.modes || {};
    res.json({ modes });
  } catch (e) {
    console.error('[Configs] Failed to read config:', e.message);
    res.status(500).json({ error: 'failed to read config' });
  }
});

module.exports = router;
