/**
 * Authentication API routes
 * Handles CSRF token issuance and credential validation
 */

const express = require('express');
const { expressBasicAuth } = require('../auth/authMiddleware');
const { issueCsrfToken } = require('../auth/csrfManager');
const config = require('../utils/config');

const router = express.Router();

/**
 * POST /api/auth/csrf
 * Issues a new CSRF token (requires Basic Auth)
 */
router.post('/csrf', expressBasicAuth, (req, res) => {
  try {
    const token = issueCsrfToken();
    
    console.log('[Auth] Issued CSRF token');
    res.json({ token, ttlMs: config.CSRF_TOKEN_TTL_MS });
    
  } catch (err) {
    console.error('[Auth] Error issuing CSRF token:', err.message);
    res.status(500).json({ error: String(err) });
  }
});

/**
 * POST /api/auth/validate
 * Validates credentials (does NOT require CSRF)
 */
router.post('/validate', expressBasicAuth, (req, res) => {
  console.log('[Auth] Credentials validated');
  res.json({ ok: true });
});

module.exports = router;
