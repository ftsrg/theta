# theta-ui Backend

Express-based API for generic software verification and managing multiple Theta versions.

## Endpoints

### Auth
All `/api/*` routes require HTTP Basic Auth if `backend/config/credentials.json` exists with:
```
{
  "username": "user",
  "password": "pass"
}
```

### GET /api/examples
List available example source files.

### GET /api/examples/{path}
Retrieve file content.

### POST /api/theta/build
Body: `{ "version": "vX.Y" | "commit", "repo?": "override_url" }`
Builds and caches the specified Theta version.

### GET /api/theta/versions
List cached versions.

### POST /api/verify
Body:
```
{
  "code": "...",
  "binaryName": "theta" | "customVerifier",
  "args": ["--domain", "PRED_CART"],
  "thetaVersion": "vX.Y" // required when binaryName === 'theta'
}
```
Returns JSON `{ code, stdout, stderr, error?, meta }`.

### GET /api/health
Simple health check.

## Environment Variables
See root `README.md` for detailed list.

## Whitelist Configuration
`backend/config/whitelist.json` governs allowed binaries. Modify with care. Only whitelisted binaries can be executed.

## Theta Build Strategy
1. Clone shallow by tag/branch; fallback to full clone for commits.
2. Patch `JAVA_VERSION` to 21 if necessary.
3. Run Gradle wrapper (or system gradle) `assemble`.
4. Cache directory retained under `THETA_CACHE_DIR`.
5. Prune oldest versions if count exceeds `MAX_THETA_VERSIONS`.

## Security Notes
- Arguments sanitized via regex: `^[a-zA-Z0-9._\-=/,:+]+$`.
- Per-process timeout and output buffer limits applied.
- Temporary source file removed after execution.

## Development
```
# Ensure Node 18 (matches Docker + avoids ICU issues)
npm install
npm run dev
```

If you encounter `node: error while loading shared libraries: libicui18n.so.*` your host Node install
is missing ICU. Recommended fixes:

1. Use nvm:
```
nvm install 18
nvm use 18
```
2. Or reinstall via NodeSource script (Debian/Ubuntu):
```
curl -fsSL https://deb.nodesource.com/setup_18.x | sudo -E bash -
sudo apt-get install -y nodejs
```
3. Or run via Docker (no host Node needed):
```
docker compose up --build
```

## Future Enhancements
- Per-binary argument schema validation.
- Sandboxed runtime via container or seccomp.
- Structured result model (JSON graph for Theta outputs).
- Add automated tests (verification mocks + Theta cache pruning).
