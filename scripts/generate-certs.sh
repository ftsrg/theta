#!/bin/bash

# Generate self-signed SSL certificates for theta-ui backend
# Usage: ./scripts/generate-certs.sh

set -e

SCRIPT_DIR="$( cd "$( dirname "${BASH_SOURCE[0]}" )" && pwd )"
PROJECT_ROOT="$( cd "$SCRIPT_DIR/.." && pwd )"
CERTS_DIR="$PROJECT_ROOT/backend/certs"

echo "=========================================="
echo "Generating self-signed SSL certificates"
echo "=========================================="
echo "Certificates will be saved to: $CERTS_DIR"
echo ""

# Create certs directory if it doesn't exist
mkdir -p "$CERTS_DIR"

# Generate private key and certificate
openssl req -x509 -newkey rsa:4096 -keyout "$CERTS_DIR/key.pem" -out "$CERTS_DIR/cert.pem" \
  -days 365 -nodes \
  -subj "/C=US/ST=State/L=City/O=Organization/CN=localhost"

echo ""
echo "=========================================="
echo "Certificates generated successfully!"
echo "=========================================="
echo "Private key: $CERTS_DIR/key.pem"
echo "Certificate: $CERTS_DIR/cert.pem"
echo "Valid for: 365 days"
echo ""
echo "Note: These are self-signed certificates."
echo "Browsers will show a security warning."
echo "You'll need to accept the certificate to proceed."
echo "=========================================="
