#!/usr/bin/env bash
# Bound Lake/Lean parallelism by the VM's memory, not only its vCPUs.
#
#   threads = clamp(floor(MemTotal_GiB / PER_PROCESS_GiB), 2, min(nproc, 8))
#
# Lake runs up to LEAN_NUM_THREADS Lean (or clang) processes at once, and each
# heavy importer/audit module peaks at 1.7-2.7 GiB RSS. lean.ci sizes VMs by
# learned memory, so an 8-vCPU VM can boot with ~11 GiB (10941 MiB, no swap):
# eight processes there failed with ENOMEM (error code 12) at exec/fork, while
# eight on >= 14973 MiB VMs passed. PER_PROCESS = 3 GiB is the 2.7 GiB peak plus
# 0.3 GiB for the fork/exec of solc or clang, the Lake driver and the OS, so
# even `threads` concurrent peaks fit: 10941 MiB -> 3, 14973 -> 4, 15981 -> 5,
# 20997 -> 6, >= 24 GiB -> 8. The cap of 8 stays: lean.ci may burst the 8-vCPU
# label to 32 vCPUs without matching memory.
#
# lean.ci learns memory from recent peaks, so fewer threads can mean smaller
# VMs next time (down to the floor of 2). The printed MemTotal makes that
# visible; the lean.ci-side fix is to count exec/fork ENOMEM as an OOM.
#
# Same targets and steps; only how many run at once changes. Writes
# LEAN_NUM_THREADS to $GITHUB_ENV (when set) and prints the inputs.
#
# Test hooks: CI_LEAN_THREADS_MEMINFO (default /proc/meminfo),
# CI_LEAN_THREADS_NPROC (default `nproc`).
set -euo pipefail

per_process_mib=3072
max_threads=8
min_threads=2

meminfo="${CI_LEAN_THREADS_MEMINFO:-/proc/meminfo}"
mem_total_kib="$(awk '$1 == "MemTotal:" { print $2 }' "$meminfo")"
if ! [[ "$mem_total_kib" =~ ^[0-9]+$ ]]; then
  echo "::error title=Lean thread bound::cannot read MemTotal from $meminfo" >&2
  exit 1
fi
vcpus="${CI_LEAN_THREADS_NPROC:-$(nproc)}"

mem_total_mib=$(( mem_total_kib / 1024 ))
threads=$(( mem_total_mib / per_process_mib ))
upper=$(( vcpus < max_threads ? vcpus : max_threads ))
(( threads > upper )) && threads=$upper
(( threads < min_threads )) && threads=$min_threads

echo "vCPUs: ${vcpus}, MemTotal: ${mem_total_mib} MiB, budget: ${per_process_mib} MiB/process -> LEAN_NUM_THREADS=${threads}"
if [ -r /proc/sys/vm/overcommit_memory ] && [ -z "${CI_LEAN_THREADS_MEMINFO:-}" ]; then
  echo "vm.overcommit_memory: $(cat /proc/sys/vm/overcommit_memory)"
  grep -E '^(CommitLimit|Committed_AS):' /proc/meminfo || true
  free -m || true
fi
if [ -n "${GITHUB_ENV:-}" ]; then
  echo "LEAN_NUM_THREADS=${threads}" >> "$GITHUB_ENV"
fi
