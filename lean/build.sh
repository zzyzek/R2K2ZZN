#!/usr/bin/env bash
# Build with a memory cap (16 GB) and 4 threads. Usage: ./build.sh [targets...]
cd "$(dirname "$0")"
exec systemd-run --user --scope -q -p MemoryMax=16G env LEAN_NUM_THREADS=4 lake build "$@"
