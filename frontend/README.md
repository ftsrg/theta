# theta-ui Frontend

React + Vite UI for editing source code, selecting examples, configuring verification runs, and managing Theta versions.

## Features
- Monaco-based code editor.
- Recursive example file tree.
- Theta version selection & on-demand build (tag or commit).
- Generic CLI argument configuration.
- Output tabs for stdout/stderr/meta.

## Dev
```
npm install
npm run dev
```
Set `VITE_API_ROOT` to your backend origin (e.g. `http://localhost:5175`).

## Build
```
npm run build
```
Outputs to `dist/`.

## Environment Variable
`VITE_API_ROOT` injected at build time.

## Extending
Add new visualizations or parsed result tabs by modifying `OutputTabs.jsx`.
