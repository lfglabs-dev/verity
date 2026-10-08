import Compiler.SolidityImport.AbiLowering
import Verity.Core.Model.Denote

namespace SolidityImportSmoke.AbiLoweringChecks
open Compiler.CompilationModel Compiler.CompilationModel.Denote
open Compiler.CompilationModel.SolidityImport.AbiLowering

def oracle : DenoteOracle := ⟨fun _ _ => 0, fun _ _ _ => 0⟩
def entryState (args : List Nat) : DenoteState :=
  { world := withTransactionContext Verity.defaultState
      { sender := 1, functionSelector := 0, args }
    bindings := [] }

theorem overlapping_head_exec :
    execStmtList oracle [] (entryState [0, 64, 0]) (tupleHead "market" 1 0 2) =
      .continue { entryState [0, 64, 0] with bindings := [("market", 4)] } := by rfl

theorem unaligned_head_exec :
    execStmtList oracle [] (entryState [1, 0, 0]) (tupleHead "market" 1 0 2) =
      .continue { entryState [1, 0, 0] with bindings := [("market", 5)] } := by rfl

theorem truncated_head_exec :
    execStmtList oracle [] (entryState [0]) (tupleHead "market" 1 0 2) =
      .revertWithData [] := by rfl

theorem overflowing_offset_exec :
    execStmtList oracle [] (entryState [2^64, 0, 0]) (tupleHead "market" 1 0 2) =
      .revertWithData [] := by rfl

def arrayBody : List Stmt :=
  staticArrayHead (.literal 68) 3 4 "array_header" "array_length" "array_data" ++
    [.return (.localVar "array_data")]

theorem backwards_array_exec :
    (match execStmtList oracle []
      (entryState [64, 1, 31337, 2, 3, 2^256-32, 999, 500, 4, 5, 1, 6, 77, 88, 9])
      arrayBody with | .return value _ => some value | _ => none) = some 68 := by rfl

theorem canonical_array_exec :
    (match execStmtList oracle []
      (entryState [64, 1, 31337, 2, 3, 256, 999, 500, 4, 5, 1, 6, 77, 88, 9])
      arrayBody with | .return value _ => some value | _ => none) = some 356 := by rfl

theorem truncated_array_exec :
    execStmtList oracle []
      (entryState [64, 1, 31337, 2, 3, 256, 999, 500, 4, 5, 1, 6, 77, 88])
      arrayBody = .revertWithData [] := by rfl

theorem excessive_array_length_exec :
    execStmtList oracle []
      (entryState [64, 1, 31337, 2, 3, 256, 999, 500, 4, 5, 2^64, 6, 77, 88, 9])
      arrayBody = .revertWithData [] := by rfl

def memoryArrayBody : List Stmt :=
  memoryStaticArrayHead (.literal 68) (.literal 384) 3 4
    "array_header" "array_length" "array_data" "next_free" ++
    [.return (.localVar "next_free")]

theorem memory_array_allocation_exec :
    (match execStmtList oracle []
      (entryState [64, 1, 31337, 2, 3, 256, 999, 500, 4, 5, 1, 6, 77, 88, 9])
      memoryArrayBody with | .return value _ => some value | _ => none) = some 448 := by rfl

theorem memory_backwards_array_exec :
    execStmtList oracle []
      (entryState [64, 1, 31337, 2, 3, 2^256-32, 999, 500, 4, 5, 1, 6, 77, 88, 9])
      memoryArrayBody = .revertWithData [] := by rfl

theorem memory_truncated_array_exec :
    execStmtList oracle []
      (entryState [64, 1, 31337, 2, 3, 256, 999, 500, 4, 5, 1, 6, 77, 88])
      memoryArrayBody = .revertWithData [] := by rfl

theorem memory_allocation_before_truncation_exec :
    execStmtList oracle []
      (entryState [64, 1, 31337, 2, 3, 256, 999, 500, 4, 5, 2^64])
      memoryArrayBody =
    .revertWithData ([0x4e, 0x48, 0x7b, 0x71] ++ List.replicate 31 0 ++ [0x41]) := by rfl

def materializedArrayBody : List Stmt :=
  memoryStaticArrayHead (.literal 68) (.literal 384) 3 4
    "array_header" "array_length" "array_data" "next_free" ++
  materializeStaticStructArray (.localVar "array_data") (.localVar "array_length")
    (.literal 384) (.localVar "next_free") "collateral"
    [.address, .uint ⟨31, by decide⟩, .uint ⟨31, by decide⟩, .address] ++
  [.returnValues ([64, 384, 416, 448, 480, 512, 544].map fun n => .mload (.literal n))]

theorem materialized_struct_array_exec :
    (match execStmtList oracle []
      (entryState [64, 1, 31337, 2, 3, 256, 999, 500, 4, 5, 1, 6, 77, 88, 9])
      materializedArrayBody with
      | .stop state => state.observedReturnWords
      | _ => none) = some [576, 1, 448, 6, 77, 88, 9] := by decide +kernel

private theorem emptyRevert_of_observation (result : StmtOutcome)
    (h : (match result with | .revertWithData data => some data | _ => none) =
      some ([] : List UInt8)) : result = .revertWithData [] := by
  cases result <;> simp_all

theorem materialized_unused_oracle_rejected :
    execStmtList oracle []
      (entryState [64, 1, 31337, 2, 3, 256, 999, 500, 4, 5, 1, 6, 77, 88, 2^160])
      materializedArrayBody = .revertWithData [] := by
  apply emptyRevert_of_observation
  decide +kernel

end SolidityImportSmoke.AbiLoweringChecks
