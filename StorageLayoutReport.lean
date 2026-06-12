/-
  StorageLayoutReport: storage layout audit JSON emitter (#1897)

  Top-level executable that prints the storage layout JSON for
  `Compiler.Specs.allSpecs` (the canonical production contract surface).
  The output feeds `scripts/generate_storage_layout_report.py`, which
  pretty-prints it into `artifacts/storage_layout_report.json` and renders
  the human-readable summary in `artifacts/STORAGE_LAYOUT_SUMMARY.md`.

  Lives at the package root rather than under `Compiler/` because it must
  import both `Compiler.CompilationModel` and `Contracts.Specs`; the
  Compiler -> Contracts boundary check enforced by
  `scripts/check_compiler_contract_imports.py` forbids that combination
  inside `Compiler/`. `PrintAxioms.lean` uses the same root-level
  placement for the same reason.

  See AUDIT.md for the audit-artifact registry.
-/
import Compiler.CompilationModel
import Compiler.CompilationModel.LayoutReport
import Contracts.Specs

open Compiler.CompilationModel
open Compiler.Specs

def main : IO Unit := do
  IO.println (emitLayoutReportJson allSpecs)
