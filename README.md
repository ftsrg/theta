# theta-ui

A generalized, containerized frontend + backend demo tool for software verification.

This is an extraction of the original CIR demo, trimmed of CIR/LLVM/xcfa-mapper specifics. It focuses on:

- Running a whitelisted verification binary with user-provided CLI arguments safely.
- Managing and caching multiple versions (git tags or commit IDs) of Theta (built via Gradle) on demand.
- Presenting code examples and a code editor in the browser, allowing on-the-fly verification runs.

## High-Level Architecture

```
theta-ui/
  backend/        <- Node.js Express server (verification API, Theta version cache)
  frontend/       <- React + MUI + Monaco based UI (examples, editor, verification controls)
  examples/       <- Copied sample examples (add more as needed)
  docker-compose.yml
```

## Core Features

- Example discovery and loading (recursive list of `.c` / `.cpp` files under `examples/`).
- Generic verification endpoint: POST `/api/verify` (code + binary + args + optional Theta version).
- Theta version management: build & cache by tag or commit, prune old versions when exceeding a limit.
- Strict binary whitelist: only configured allowed binaries can be launched.
- Timeout + argument sanitization for safety.

## Quick Start (Local, Non-Docker)

Prereqs: Node.js 18 (recommended), Git, JDK 21 (for Theta build), bash.

```
cd theta-ui/backend
npm install
npm start
```

In a second terminal:
```
cd theta-ui/frontend
npm install
npm run dev
```

Visit http://localhost:5175 (backend default) & http://localhost:5176 (frontend dev default/dev server may vary).

Set `VITE_API_ROOT=http://localhost:5175` for the frontend if needed.

If you see an error like:
```
node: error while loading shared libraries: libicui18n.so.*: cannot open shared object file
```
your host Node install is missing ICU libraries. Solutions:
1. Use nvm and install Node 18 (`nvm install 18 && nvm use 18`).
2. Reinstall via NodeSource: `curl -fsSL https://deb.nodesource.com/setup_18.x | sudo -E bash - && sudo apt-get install -y nodejs`.
3. Or skip local setup and use Docker Compose.

## Docker Compose

```
cd theta-ui
docker compose up --build
```
Front-end is exposed by default on port 8080 (adjust in compose file).

## Environment Variables (Backend)

- `PORT` (default: 5175) API listening port.
- `BASIC_AUTH_FILE` path to credentials JSON (`{"username":"u","password":"p"}`) for basic auth protection.
- `THETA_REPO_URL` (default: https://github.com/ftsrg/theta.git)
- `THETA_CACHE_DIR` (default: data/theta-cache inside backend)
- `MAX_THETA_VERSIONS` (default: 5) maximum cached versions before pruning LRU/oldest.
- `EXEC_TIMEOUT_MS` (default: 30000) per process timeout.

## Security Model

- Only binaries declared in `backend/config/whitelist.json` are executable.
- Arguments filtered by regex `^[a-zA-Z0-9._\-=/,:+]+$`.
- Source code placed in a temporary file with a generated basename; no user-controlled path traversal.
- Timeouts applied to child processes; output buffers capped.

## Adding More Examples

Copy additional `.c` or `.cpp` files under `examples/`. They will be auto-discovered.

## Extending Verification

1. Add a new binary entry to `backend/config/whitelist.json` (type `raw`).
2. Rebuild/restart backend.
3. Use the frontend controls to select and run with approved args.

For Theta variants, no change needed: specify a new tag or commit in the frontend. Backend builds & caches it.

## Future Improvements

- Sandbox execution using containers or Firecracker/MicroVM.
- Resource limits (CPU/memory) via cgroups.
- More granular argument schema/validation per binary.
- Persist run history with search & diff.

## License

Matches the parent repository unless otherwise stated.
