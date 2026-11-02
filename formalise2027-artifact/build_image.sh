#!/usr/bin/env bash
# Build the Docker image for linux/amd64 and linux/arm64, export the amd64 image
# as a tar archive, and write the SHA256 checksum required by the artifact track.
set -euo pipefail
cd "$(dirname "$0")"
TAG=cakeml-lean-migration:1.0
docker buildx build --platform linux/amd64 -t "$TAG" --load .
docker save "$TAG" | gzip > cakeml-lean-migration-1.0-amd64.tar.gz
# Optional multi-platform build (needs a buildx builder with QEMU):
#   docker buildx build --platform linux/amd64,linux/arm64 -t "$TAG" .
sha256sum cakeml-lean-migration-1.0-amd64.tar.gz > cakeml-lean-migration-1.0-amd64.tar.gz.sha256
echo "wrote cakeml-lean-migration-1.0-amd64.tar.gz"
