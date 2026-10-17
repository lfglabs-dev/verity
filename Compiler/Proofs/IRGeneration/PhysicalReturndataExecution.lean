import Compiler.Proofs.IRGeneration.PhysicalReturndataBytes
import Compiler.Proofs.IRGeneration.IRInterpreter

namespace Compiler.Proofs.IRGeneration.PhysicalReturndataExecution
open Compiler.Yul Compiler.CompilationModel

def body : List YulStmt :=
  [.block [
    .let_ "__returndata_size" (.call "returndatasize" []),
    .exprStmt (.call "returndatacopy" [.lit 0, .lit 0, .ident "__returndata_size"]),
    .exprStmt (.call "revert" [.lit 0, .ident "__returndata_size"])]]

/-- Actual bubbling code executes the copy and capture; the extent bound
prevents the opcode's uint256 size normalization from truncating the buffer. -/
theorem execute (state : IRState) (extra : Nat)
    (extent : 32 * state.returndata.length < Verity.Core.Uint256.modulus) :
    execIRStmts (extra + 6) state body =
      .revert (((state.setVar "__returndata_size" (32 * state.returndata.length)).copyPhysicalReturndata 0 0 (32 * state.returndata.length)).captureRevert
          0 (32 * state.returndata.length)) := by
  have fuel : extra + 6 = Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ extra))))) := by omega
  have normalized : 32 * state.returndata.length % Compiler.Constants.evmModulus =
      32 * state.returndata.length := Nat.mod_eq_of_lt extent
  rw [fuel]
  simp [body, execIRStmts, execIRStmt, evalIRExpr, IRState.getVar, IRState.setVar, IRState.copyPhysicalReturndata,
    IRState.copyPhysicalBytes, IRState.installPhysicalMemory,
    normalized]
  split_ifs <;> rfl

/-- Sufficient execution fuel and a nontruncated extent give the complete
Source payload, with no bound on the legacy natural-number word values. -/
theorem execute_payload_unbounded (state : IRState) (extra : Nat)
    (extent : 32 * state.returndata.length < Verity.Core.Uint256.modulus) :
    ∃ final, execIRStmts (extra + 6) state body = .revert final ∧
      final.revertBytes = some (state.returndata.flatMap Denote.wordBytes) := by
  refine ⟨_, execute state extra extent, ?_⟩
  exact PhysicalReturndataBytes.captured_buffer_unbounded
    (state.setVar "__returndata_size" (32 * state.returndata.length))

theorem execute_payload (state : IRState) (extra : Nat)
    (extent : 32 * state.returndata.length < Verity.Core.Uint256.modulus)
    (_bounded : ∀ value ∈ state.returndata, value < Verity.Core.Uint256.modulus) :
    ∃ final, execIRStmts (extra + 6) state body = .revert final ∧
      final.revertBytes = some (state.returndata.flatMap Denote.wordBytes) :=
  execute_payload_unbounded state extra extent

end Compiler.Proofs.IRGeneration.PhysicalReturndataExecution
