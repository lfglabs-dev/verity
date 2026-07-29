#!/usr/bin/env bash
set -euo pipefail

# Skip ccache for link invocations (ccache cannot cache them).
# Detect linking by checking if -c flag is absent — compilation passes
# always include -c, while link invocations never do.
is_compile=false
for arg in "$@"; do
  if [ "$arg" = "-c" ]; then
    is_compile=true
    break
  fi
done

if $is_compile; then
  exec ccache clang -fuse-ld=lld "$@"
else
  # Lean 4.31's distributed runtime archives use libc++ (`std::__1`).
  # Invoke the C driver as Lake expects, but supply the matching C++ runtime
  # explicitly for final executable links.
  exec clang -fuse-ld=lld "$@" -lc++ -lc++abi
fi
