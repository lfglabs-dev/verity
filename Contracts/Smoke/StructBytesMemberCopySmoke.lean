import Contracts.Common
import Contracts.ProofKit

namespace Contracts.Smoke

open Verity hiding pure bind

/-! `copyBytes` and `bytesLength` on a `Bytes` member of a dynamically encoded struct
parameter lower through the checked dynamic-member helpers (`paramDynamicMemberDataOffset`
/ `paramDynamicMemberLength`), like `arrayLength s.field`. -/
verity_contract StructBytesMemberCopySmoke where
  storage

  struct Call where
    target : Address,
    data : Bytes,
    tag : Uint256

  function copyData (c : Call)
    local_obligations [scratch_copy := assumed "copies the member to memory at 0x80 and reads the first word back"]
    : Uint256 := do
    copyBytes c.data 128
    let w := mload 128
    return w

  function hashData (c : Call)
    local_obligations [scratch_hash := assumed "copies the member to memory at 0x80 and hashes the copied region"]
    : Uint256 := do
    copyBytes c.data 128
    let h := keccak256 128 (bytesLength c.data)
    return h

  function dataLength (c : Call) : Uint256 := do
    return bytesLength c.data

example :
    StructBytesMemberCopySmoke.copyData_modelBody =
      [ Compiler.CompilationModel.Stmt.calldatacopy
          (Compiler.CompilationModel.Expr.literal 128)
          (Compiler.CompilationModel.Expr.paramDynamicMemberDataOffset "c" 1)
          (Compiler.CompilationModel.Expr.paramDynamicMemberLength "c" 1)
      , Compiler.CompilationModel.Stmt.letVar "w"
          (Compiler.CompilationModel.Expr.mload (Compiler.CompilationModel.Expr.literal 128))
      , Compiler.CompilationModel.Stmt.return (Compiler.CompilationModel.Expr.localVar "w")
      ] := rfl

example :
    StructBytesMemberCopySmoke.dataLength_modelBody =
      [ Compiler.CompilationModel.Stmt.return
          (Compiler.CompilationModel.Expr.paramDynamicMemberLength "c" 1)
      ] := rfl

open Contracts.ProofKit in
/-- Executable side: `hashData c` returns `keccak256(c.data)` for every struct `c`: the whole
copied region is hashed, not only its first word. -/
theorem hashData_is_keccak (c : StructBytesMemberCopySmoke.Call) (s : ContractState)
    (hsize : 128 + c.data.size + 32 < 2 ^ 256) :
    ∃ s', StructBytesMemberCopySmoke.hashData c s =
      .success (Verity.Core.Uint256.ofNat (keccakBytes c.data.data.toList)) s' := by
  unfold StructBytesMemberCopySmoke.hashData
  obtain ⟨u, s1, h1⟩ : ∃ u s1, Contracts.copyBytes c.data 128 s = .success u s1 :=
    ⟨_, _, copyBytes_run _ _ _⟩
  rw [bind_step h1, bind_step (keccak256Live_eq _ _ _), keccak_after_copyBytes h1 hsize]
  exact ⟨_, rfl⟩

/-- Executable side: the member's bytes land in memory. -/
example :
    let c : StructBytesMemberCopySmoke.Call := { target := 0, data := ⟨#[0xab]⟩, tag := 0 }
    ((StructBytesMemberCopySmoke.copyData c).run Verity.defaultState).getValue? =
      some 0xab00000000000000000000000000000000000000000000000000000000000000 := by
  rfl

example :
    let c : StructBytesMemberCopySmoke.Call := { target := 0, data := ⟨#[1, 2, 3]⟩, tag := 0 }
    ((StructBytesMemberCopySmoke.dataLength c).run Verity.defaultState).getValue? = some 3 := by
  rfl

end Contracts.Smoke
