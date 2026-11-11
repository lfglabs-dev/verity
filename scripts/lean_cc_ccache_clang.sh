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

lean_prefix="${LEAN_SYSROOT:-$(lean --print-prefix)}"
lean_clang="${lean_prefix}/bin/clang"

if $is_compile; then
  if command -v ccache >/dev/null 2>&1; then
    exec ccache "$lean_clang" -B "$lean_prefix/bin" -fuse-ld=lld "$@"
  else
    exec "$lean_clang" -B "$lean_prefix/bin" -fuse-ld=lld "$@"
  fi
else
  # Use the compiler shipped with Lean: its libc++ ABI matches the distributed
  # Lean 4.31 runtime archives, unlike an independently installed host clang.
  # Link libunwind statically so packaged binaries do not retain the builder's
  # absolute Lean prefix in DT_RUNPATH.
  exec "$lean_clang" -B "$lean_prefix/bin" -fuse-ld=lld -L "$lean_prefix/lib" \
    "$@" "$lean_prefix/lib/libunwind.a"
fi
