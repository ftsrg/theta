/**
 * CSRF token management module
 * Handles generation, validation, and expiry of CSRF tokens
 */

const config = require('../utils/config');

// In-memory token store: token -> expiry timestamp
const csrfTokens = new Map();

/**
 * Generates a random CSRF token
 * @returns {string} Generated token
 */
function generateCsrfToken() {
  const token = 'csrf_' + 
    Math.random().toString(36).slice(2) + 
    Math.random().toString(36).slice(2);
  
  console.log('[CSRF] Generated new token');
  return token;
}

/**
 * Issues a new CSRF token with expiry
 * @returns {string} Issued token
 */
function issueCsrfToken() {
  const token = generateCsrfToken();
  const expiry = Date.now() + config.CSRF_TOKEN_TTL_MS;
  csrfTokens.set(token, expiry);
  
  console.log(`[CSRF] Issued token (expires in ${config.CSRF_TOKEN_TTL_MS}ms)`);
  return token;
}

/**
 * Validates a CSRF token
 * @param {string} token - Token to validate
 * @returns {boolean} True if valid, false otherwise
 */
function validateCsrfToken(token) {
  if (!token) {
    console.warn('[CSRF] Validation failed: no token provided');
    return false;
  }
  
  const exp = csrfTokens.get(token);
  
  if (!exp) {
    console.warn('[CSRF] Validation failed: token not found');
    return false;
  }
  
  if (Date.now() > exp) {
    csrfTokens.delete(token);
    console.warn('[CSRF] Validation failed: token expired');
    return false;
  }
  
  console.log('[CSRF] Token validated successfully');
  return true;
}

/**
 * Removes expired CSRF tokens from memory
 */
function pruneCsrfTokens() {
  const now = Date.now();
  let prunedCount = 0;
  
  for (const [tok, exp] of csrfTokens.entries()) {
    if (exp < now) {
      csrfTokens.delete(tok);
      prunedCount++;
    }
  }
  
  if (prunedCount > 0) {
    console.log(`[CSRF] Pruned ${prunedCount} expired token(s)`);
  }
}

/**
 * Initializes periodic pruning of expired tokens
 */
function initializePruning() {
  setInterval(pruneCsrfTokens, 5 * 60 * 1000).unref();
  console.log('[CSRF] Initialized periodic token pruning (every 5 minutes)');
}

module.exports = {
  issueCsrfToken,
  validateCsrfToken,
  initializePruning
};
