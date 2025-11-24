#!/bin/bash

# Build script for theta-ui frontend with configurable backend location
# Usage: ./scripts/build-frontend.sh [API_ROOT]
# Example: ./scripts/build-frontend.sh https://theta.example.com

set -e

# Get the script directory and project root
SCRIPT_DIR="$( cd "$( dirname "${BASH_SOURCE[0]}" )" && pwd )"
PROJECT_ROOT="$( cd "$SCRIPT_DIR/.." && pwd )"
FRONTEND_DIR="$PROJECT_ROOT/frontend"
BUILD_OUTPUT="$FRONTEND_DIR/dist"

# Parse arguments
API_ROOT="${1:-https://localhost:5175}"

echo "=========================================="
echo "Building theta-ui frontend"
echo "=========================================="
echo "API Root: $API_ROOT"
echo "Frontend Dir: $FRONTEND_DIR"
echo "Output Dir: $BUILD_OUTPUT"
echo "=========================================="

# Check if frontend directory exists
if [ ! -d "$FRONTEND_DIR" ]; then
  echo "Error: Frontend directory not found at $FRONTEND_DIR"
  exit 1
fi

# Check if node_modules exists, install if needed
if [ ! -d "$FRONTEND_DIR/node_modules" ]; then
  echo "Installing frontend dependencies..."
  cd "$FRONTEND_DIR"
  npm install
fi

# Build the frontend with the configured API root
cd "$FRONTEND_DIR"
echo "Building frontend with VITE_API_ROOT=$API_ROOT..."
VITE_API_ROOT="$API_ROOT" npm run build

echo "=========================================="
echo "Build complete!"
echo "Static files are in: $BUILD_OUTPUT"
echo "=========================================="
echo ""
echo "To serve the static files:"
echo "  1. Use a web server like nginx, apache, or caddy"
echo "  2. Point the web server to: $BUILD_OUTPUT"
echo "  3. Ensure CORS is configured on the backend at: $API_ROOT"
echo ""
echo "Quick test with Python:"
echo "  cd $BUILD_OUTPUT"
echo "  python3 -m http.server 8080"
echo "  # Visit http://localhost:8080"
