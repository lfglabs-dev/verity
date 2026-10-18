import Verity.Core.Model.Denote

/-!
Bridge from the closed Denote transports for `<address>.code` and the memory
`return` to `DenoteExternalCode` and `DenoteState.observedReturnWords`.

* The code-copy arm reads exactly `DenoteExternalCode.accountCode`: within the
  64-bit allocation domain it binds the free pointer and writes the advanced free
  pointer, the length word and the code bytes; a length or allocation beyond 64
  bits is exactly `Panic(0x41)`.
* The memory-return arm stops with exactly the buffer's words; a buffer that is
  not whole words is an instrumentation error.
-/
namespace Compiler.CompilationModel.DenoteExternalCodeCopy

open Compiler.CompilationModel
open Denote

/-! ## Code copy -/

theorem extCodeCopy_module_beq_self (resultVar : String) :
    (Compiler.ECM.SolidityExtCodeCopy.module resultVar ==
      Compiler.ECM.SolidityExtCodeCopy.module resultVar) = true := by
  simp [BEq.beq, Compiler.ECM.SolidityExtCodeCopy.module, List.beq]
  exact ⟨⟨⟨rfl, rfl⟩, rfl⟩,
    beq_self_eq_true (some (Compiler.ECM.ByteTransport.extCodeCopy resultVar))⟩

/-- The copied code is the account world's runtime code. -/
abbrev copiedCode (state : DenoteState) (account : Nat) : List UInt8 :=
  DenoteExternalCode.accountCode state.world (Verity.Core.Address.ofNat account)

/-- The free pointer after allocating the copied code. -/
abbrev nextFree (state : DenoteState) (account : Nat) : Nat :=
  ((state.world.memory 64).val + (((copiedCode state account).length + 31) / 32 * 32 + 32)) % 2^256

/-- Within the 64-bit allocation domain the transport binds the old free pointer
and installs the advanced free pointer, the length word and the code bytes. -/
theorem executeByteExtCodeCopy_eq (oracle : DenoteOracle) (fields : List Field)
    (state : DenoteState) (resultVar : String) (target : Expr) (account : Nat)
    (htarget : evalExprList oracle fields state [target] = some [account])
    (hlength : (copiedCode state account).length ≤ 2^64 - 1)
    (hnext : nextFree state account ≤ 2^64 - 1)
    (hmono : (state.world.memory 64).val ≤ nextFree state account) :
    executeByteExtCodeCopy oracle fields state
        (Compiler.ECM.SolidityExtCodeCopy.module resultVar) resultVar [target] =
      .ok (.continue { state with
        world := ((state.world.writePhysicalMemoryValue 64
            (Verity.Core.Uint256.ofNat (nextFree state account))).writePhysicalMemoryValue
            (state.world.memory 64).val
            (Verity.Core.Uint256.ofNat (copiedCode state account).length)).copyPhysicalMemory
          (rawPhysicalByte (copiedCode state account)) ((state.world.memory 64).val + 32) 0
          (copiedCode state account).length
        bindings := bindValue state.bindings resultVar (state.world.memory 64).val }) := by
  simp only [nextFree] at hnext hmono
  simp only [copiedCode] at hlength hnext hmono
  simp only [executeByteExtCodeCopy, htarget, extCodeCopy_module_beq_self, ↓reduceIte,
    Nat.not_lt.mpr hlength, Nat.not_lt.mpr hnext, Nat.not_lt.mpr hmono, or_self]
  rfl

/-- A code length beyond 64 bits is `Panic(0x41)`, as in solc's allocation. -/
theorem executeByteExtCodeCopy_of_length_overflow (oracle : DenoteOracle)
    (fields : List Field) (state : DenoteState) (resultVar : String) (target : Expr)
    (account : Nat) (htarget : evalExprList oracle fields state [target] = some [account])
    (hlength : 2^64 - 1 < (copiedCode state account).length) :
    executeByteExtCodeCopy oracle fields state
        (Compiler.ECM.SolidityExtCodeCopy.module resultVar) resultVar [target] =
      .ok (.revertWithData (panicBytes 0x41)) := by
  simp only [copiedCode] at hlength
  simp only [executeByteExtCodeCopy, htarget, extCodeCopy_module_beq_self, ↓reduceIte, hlength]
  rfl

/-! ## Memory return -/

theorem returnMemory_module_beq_self :
    (Compiler.ECM.SolidityReturnMemory.module ==
      Compiler.ECM.SolidityReturnMemory.module) = true := by
  simp [BEq.beq, Compiler.ECM.SolidityReturnMemory.module]
  exact ⟨⟨⟨rfl, rfl⟩, rfl⟩, beq_self_eq_true (some Compiler.ECM.ByteTransport.returnMemory)⟩

/-- A whole-word buffer stops the frame with exactly its words, in order. -/
theorem executeByteReturnMemory_eq (oracle : DenoteOracle) (fields : List Field)
    (state : DenoteState) (offsetExpr sizeExpr : Expr) (offset size : Nat)
    (hargs : evalExprList oracle fields state [offsetExpr, sizeExpr] = some [offset, size])
    (haligned : size % 32 = 0) :
    executeByteReturnMemory oracle fields state Compiler.ECM.SolidityReturnMemory.module
        [offsetExpr, sizeExpr] =
      .ok (.stop { state with
        observedReturnWords := some ((List.range (size / 32)).map fun index =>
          (DenoteMemory.wordValue (state.world.byteMemory.readWord (offset + 32 * index))).val)
        observedStop := false }) := by
  simp only [executeByteReturnMemory, hargs, returnMemory_module_beq_self, ↓reduceIte, haligned]
  rfl

/-- A buffer that is not whole words is an instrumentation error, never a return. -/
theorem executeByteReturnMemory_unaligned (oracle : DenoteOracle) (fields : List Field)
    (state : DenoteState) (offsetExpr sizeExpr : Expr) (offset size : Nat)
    (hargs : evalExprList oracle fields state [offsetExpr, sizeExpr] = some [offset, size])
    (hunaligned : size % 32 ≠ 0) :
    executeByteReturnMemory oracle fields state Compiler.ECM.SolidityReturnMemory.module
        [offsetExpr, sizeExpr] = .error "returned memory is not word aligned" := by
  have hbeq : (size % 32 == 0) = false := by simp [hunaligned]
  simp only [executeByteReturnMemory, hargs, returnMemory_module_beq_self, ↓reduceIte, hbeq]
  rfl

end Compiler.CompilationModel.DenoteExternalCodeCopy
