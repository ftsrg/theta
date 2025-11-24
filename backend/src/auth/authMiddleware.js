/**
 * Authentication middleware module
 * Handles Basic Auth verification and credential management
 */

const { loadJSONSync } = require('../utils/fileUtils');
const config = require('../utils/config');

/**
 * Loads credentials from the credentials file
 * @returns {{username: string, password: string}|null}
 */
function loadCredsSync() {
  const parsed = loadJSONSync(config.BASIC_AUTH_FILE, null);
  
  if (!parsed) {
    console.error('[Auth] No credentials found in credentials file');
    return null;
  }
  
  if (!parsed.username || !parsed.password) {
    console.error('[Auth] Invalid credentials format in credentials file');
    return null;
  }
  
  return {
    username: String(parsed.username || ''),
    password: String(parsed.password || '')
  };
}

/**
 * Sends unauthorized response with WWW-Authenticate header
 * @param {object} res - Express response object
 */
function unauthorized(res) {
  res.setHeader('WWW-Authenticate', 'Basic realm="theta-ui"');
  return res.status(401).send('Unauthorized');
}

/**
 * Express middleware for Basic Authentication
 * Validates credentials against stored credentials file
 * @param {object} req - Express request object
 * @param {object} res - Express response object
 * @param {function} next - Express next function
 */
function expressBasicAuth(req, res, next) {
  const creds = loadCredsSync();
  
  if (!creds || !creds.username) {
    console.error('[Auth] No valid credentials configured');
    return unauthorized(res);
  }
  
  const auth = req.headers['authorization'];
  
  if (!auth || !auth.startsWith('Basic ')) {
    console.warn('[Auth] Missing or invalid Authorization header');
    return unauthorized(res);
  }
  
  const token = auth.slice('Basic '.length);
  let decoded;
  
  try {
    decoded = Buffer.from(token, 'base64').toString('utf8');
  } catch (err) {
    console.error('[Auth] Failed to decode Authorization token:', err.message);
    return unauthorized(res);
  }
  
  const idx = decoded.indexOf(':');
  
  if (idx === -1) {
    console.warn('[Auth] Invalid Authorization token format');
    return unauthorized(res);
  }
  
  const u = decoded.slice(0, idx);
  const p = decoded.slice(idx + 1);
  
  if (u === creds.username && p === creds.password) {
    console.log(`[Auth] Successful authentication for user: ${u}`);
    return next();
  } else {
    console.warn(`[Auth] Failed authentication attempt for user: ${u}`);
    return unauthorized(res);
  }
}

module.exports = {
  expressBasicAuth,
  loadCredsSync
};
