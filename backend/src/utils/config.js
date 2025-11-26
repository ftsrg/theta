/**
 * Configuration module - centralizes all application configuration
 * Loads environment variables and defines constants used throughout the application
 */

const path = require('path');

// Server configuration
const PORT = process.env.PORT || 5175;
const USE_HTTPS = process.env.USE_HTTPS !== 'false';
const CERT_FILE = process.env.CERT_FILE || path.join(__dirname, '..', '..', 'certs', 'cert.pem');
const KEY_FILE = process.env.KEY_FILE || path.join(__dirname, '..', '..', 'certs', 'key.pem');

// Authentication configuration
const BASIC_AUTH_FILE = process.env.BASIC_AUTH_FILE || path.join(__dirname, '..', '..', 'config', 'credentials.json');
const CSRF_TOKEN_TTL_MS = 30 * 60 * 1000; // 30 minutes

// Application paths
const WHITELIST_FILE = path.join(__dirname, '..', '..', 'config', 'whitelist.json');
const EXAMPLES_DIR = path.join(__dirname, '..', '..', '..', 'examples', 'models');
const PROPERTIES_DIR = path.join(__dirname, '..', '..', '..', 'examples', 'properties');
const THETA_CACHE_DIR = process.env.THETA_CACHE_DIR || path.join(__dirname, '..', '..', 'data', 'theta-cache');
const THETA_TEMP_DIR = path.join(__dirname, '..', '..', 'data', 'theta-temp');

// Theta configuration
const THETA_REPO_URL_DEFAULT = 'https://github.com/ftsrg/theta.git';
const MAX_THETA_VERSIONS = parseInt(process.env.MAX_THETA_VERSIONS || '5', 10);
const MAX_CACHE_SIZE = 5 * 1024 * 1024 * 1024; // 5GB in bytes

// Execution limits
const EXEC_TIMEOUT_MS = parseInt(process.env.EXEC_TIMEOUT_MS || '30000', 10);
const MAX_BUFFER = 20 * 1024 * 1024; // 20MB output cap
const MAX_FILE_SIZE = 1024 * 1024; // 1MB per file

// External APIs
const GITHUB_RELEASES_API = 'https://api.github.com/repos/ftsrg/theta/releases';

// Periodic tasks
const AUTO_RETRIEVAL_INTERVAL = 10 * 60 * 1000; // 10 minutes

// Tool paths
const BENCHEXEC_BIN = path.join(__dirname, '..', '..', '..', 'benchexec', 'bin', 'runexec');
const SV_WITNESSES_DIR = path.join(__dirname, '..', '..', '..', 'sv-witnesses');
const LIB_DIR = path.join(__dirname, '..', '..', '..', 'lib');
const BACKEND_ROOT = path.join(__dirname, '..', '..');

module.exports = {
  PORT,
  USE_HTTPS,
  CERT_FILE,
  KEY_FILE,
  BASIC_AUTH_FILE,
  CSRF_TOKEN_TTL_MS,
  WHITELIST_FILE,
  EXAMPLES_DIR,
  PROPERTIES_DIR,
  THETA_CACHE_DIR,
  THETA_TEMP_DIR,
  THETA_REPO_URL_DEFAULT,
  MAX_THETA_VERSIONS,
  MAX_CACHE_SIZE,
  EXEC_TIMEOUT_MS,
  MAX_BUFFER,
  MAX_FILE_SIZE,
  GITHUB_RELEASES_API,
  AUTO_RETRIEVAL_INTERVAL,
  BENCHEXEC_BIN,
  SV_WITNESSES_DIR,
  LIB_DIR,
  BACKEND_ROOT
};
