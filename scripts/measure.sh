#!/bin/sh
# Time a full `lake build` and propagate its exit status (the previous
# `lake build | tail` form returned tail's status, so a failed build exited 0).
set -eu
START=$(date +%s)
echo "START: $(date -Iseconds)"
LOG=$(mktemp)
set +e
lake build >"$LOG" 2>&1
STATUS=$?
set -e
tail -20 "$LOG"
rm -f "$LOG"
END=$(date +%s)
echo "DURATION: $((END-START))s"
echo "END: $(date -Iseconds)"
echo "BUILD_STATUS: $STATUS"
exit "$STATUS"
