/**
 * Main server application
 * Initializes Express server with all routes and middleware
 */

const express = require('express');
const https = require('https');
const fs = require('fs');
const cors = require('cors');
const config = require('./utils/config');
const { initializePruning } = require('./auth/csrfManager');
const { periodicMaintenance } = require('./theta/releaseManager');

// Import route modules
const examplesRoutes = require('./routes/examples');
const propertiesRoutes = require('./routes/properties');
const authRoutes = require('./routes/auth');
const thetaRoutes = require('./routes/theta');

// Ensure required directories exist
fs.mkdirSync(config.THETA_CACHE_DIR, { recursive: true });
fs.mkdirSync(config.THETA_TEMP_DIR, { recursive: true });

console.log('[Server] Initializing application...');

// Initialize CSRF token pruning
initializePruning();

// Initialize Express app
const app = express();
app.use(cors());
app.use(express.json({ limit: '1mb' }));

// Mount route modules
app.use('/api/examples', examplesRoutes);
app.use('/api/properties', propertiesRoutes);
app.use('/api/auth', authRoutes);
app.use('/api/theta', thetaRoutes);

// Mount verification routes (includes streaming verification and retrieval)
const { retrieveStreamRouter } = require('./routes/verification');
const verificationRoutes = require('./routes/verification');
app.use('/api/verify', verificationRoutes);
app.use('/api', retrieveStreamRouter); // Mounts /api/theta/retrieve/stream

// Health check endpoint
app.get('/api/health', (req, res) => {
  console.log('[Server] Health check');
  res.json({ status: 'ok' });
});

// Start periodic maintenance (release checking and cleanup)
setInterval(periodicMaintenance, config.AUTO_RETRIEVAL_INTERVAL);
setTimeout(periodicMaintenance, 10000); // Run once at startup after delay

console.log('[Server] Periodic maintenance scheduled');

// Start server
if (config.USE_HTTPS) {
  // Check if certificates exist
  if (!fs.existsSync(config.CERT_FILE) || !fs.existsSync(config.KEY_FILE)) {
    console.error('[Server] ERROR: SSL certificates not found!');
    console.error(`[Server] Certificate: ${config.CERT_FILE}`);
    console.error(`[Server] Private Key: ${config.KEY_FILE}`);
    console.error('[Server] Run: ./scripts/generate-certs.sh to create self-signed certificates');
    console.error('[Server] Or set USE_HTTPS=false to use HTTP instead');
    process.exit(1);
  }

  const httpsOptions = {
    key: fs.readFileSync(config.KEY_FILE),
    cert: fs.readFileSync(config.CERT_FILE)
  };

  https.createServer(httpsOptions, app).listen(config.PORT, () => {
    console.log(`[Server] theta-ui backend listening on https://localhost:${config.PORT}`);
    console.log('[Server] Using HTTPS with self-signed certificates');
    console.log('[Server] Note: Browsers will show security warnings for self-signed certificates');
  });
} else {
  app.listen(config.PORT, () => {
    console.log(`[Server] theta-ui backend listening on http://localhost:${config.PORT}`);
    console.log('[Server] Using HTTP (set USE_HTTPS=true to enable HTTPS)');
  });
}

module.exports = app;
