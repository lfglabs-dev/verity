import Compiler.Proofs.IRGeneration.PhysicalRevertWrites
import Compiler.CompilationModel.AbiHelpers

/-! Actual compiler-emitted Error(string) payload execution with physical memory.
This fixes the execution-state relation; proving that its complete observed
slice equals the Source ABI bytes is the subsequent encoding obligation. -/
namespace Compiler.Proofs.IRGeneration.PhysicalErrorStringExecution
open Compiler.CompilationModel Compiler.Yul PhysicalRevertWrites

def dataWrites (message : String) : List (Nat × Nat) :=
  (chunkBytes32 (bytesFromString message)).zipIdx.map
    (fun pair => (68 + pair.2 * 32, wordFromBytes pair.1))

def writes (message : String) : List (Nat × Nat) :=
  [(0, Compiler.Constants.errorStringSelectorWord), (4, 32),
    (36, (bytesFromString message).length)] ++ dataWrites message

def payloadStores (message : String) : List YulStmt :=
  [.exprStmt (.call "mstore" [.lit 0, .hex Compiler.Constants.errorStringSelectorWord]),
   .exprStmt (.call "mstore" [.lit 4, .lit 32]),
   .exprStmt (.call "mstore" [.lit 36, .lit (bytesFromString message).length])] ++
    hexStores (dataWrites message)

theorem trace (message : String) : StoreTrace (payloadStores message) (writes message) := by
  exact (StoreTrace.consHex 0 _ (StoreTrace.consLit 4 32
    (StoreTrace.consLit 36 _ StoreTrace.nil))).append (StoreTrace.hexStores _)

theorem shape (message : String) :
    revertWithMessage message = payloadStores message ++
      [.exprStmt (.call "revert" [.lit 0,
        .lit (68 + ((bytesFromString message).length + 31) / 32 * 32)])] := by
  simp only [revertWithMessage, payloadStores, hexStores, dataWrites, List.map_map]
  rfl

theorem execute (message : String) (state : IRState) (fuel : Nat) :
    execIRStmts ((writes message).length + fuel + 2) state (revertWithMessage message) =
      .revert ((applyStores state (writes message)).captureRevert 0
        (68 + ((bytesFromString message).length + 31) / 32 * 32)) := by
  rw [shape]
  exact exec_trace_revert (trace message) state fuel _ _

end Compiler.Proofs.IRGeneration.PhysicalErrorStringExecution
