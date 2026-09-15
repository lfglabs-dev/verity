#!/bin/sh
set -eu
START=$(date +%s)
echo "START: $(date -Iseconds)"
lake build 2>&1 | tail -20
END=$(date +%s)
echo "DURATION: $((END-START))s"
echo "END: $(date -Iseconds)"
