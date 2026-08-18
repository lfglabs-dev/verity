import Compiler.ABI.Frame
import Compiler.Codegen
import Compiler.CompilationModel
import Compiler.CompilationModel.Compile
import Compiler.Modules.CodeData
import Compiler.Proofs.Storage.FieldStorageKey
import Compiler.Proofs.Storage.MappingCoherence
import Compiler.Yul.PrettyPrint
import Verity.Core.Model.MultiContract

/-!
  Compile/denotation checks for the four-feature increment:
  mapping-of-fixed-array, CodeData/SSTORE2 layout, transient
  `fixedArrayUint128`, and first-class self-delegate sequences.
-/

namespace Compiler.FourFeaturesTest

open Compiler
open Compiler.ABI.Frame
open Compiler.CompilationModel
open Compiler.Modules.CodeData
open Compiler.Proofs.Storage.FieldStorageKey
open Compiler.Proofs.Storage.MappingCoherence
open Compiler.Yul
open Verity
open Verity.MultiContract
open Compiler.CompilationModel.DenoteExternalCalls

private def contains (haystack needle : String) : Bool :=
  let h := haystack.toList
  let n := needle.toList
  if n.isEmpty then true
  else
    let rec go : List Char → Bool
      | [] => false
      | c :: cs =>
          if (c :: cs).take n.length == n then true
          else go cs
    go h

private def expectTrue (label : String) (ok : Bool) : IO Unit := do
  if !ok then
    throw (IO.userError s!"✗ {label}")
  IO.println s!"✓ {label}"

private def selectorsFor (spec : CompilationModel) : List Nat :=
  List.range (spec.functions.filter (fun fn =>
    !fn.isInternal && fn.name != "fallback" && fn.name != "receive")).length

private def expectCompileToYul (label : String) (spec : CompilationModel) : IO String := do
  match compile spec (selectorsFor spec) with
  | .ok ir =>
      IO.println s!"✓ {label}"
      pure (Compiler.Yul.render (Compiler.emitYul ir))
  | .error err =>
      throw (IO.userError s!"✗ {label}: compile failed: {err}")

private def expectCompileErrorContains (label : String)
    (spec : CompilationModel) (needle : String) : IO Unit := do
  match compile spec (selectorsFor spec) with
  | .ok _ => throw (IO.userError s!"✗ {label}: expected compile error containing '{needle}'")
  | .error err =>
      if !contains err needle then
        throw (IO.userError s!"✗ {label}: expected error containing '{needle}', got '{err}'")
      IO.println s!"✓ {label}"

/-! ## FixedArray-under-mapping -/

private def mappingFixedArraySpec : CompilationModel := {
  name := "MappingFixedArraySmoke"
  fields := [
    { name := "arrs", ty := .mappingFixedArray .address 4, «slot» := some 0 }
  ]
  «constructor» := none
  functions := [
    { name := "getElem"
      params := [{ name := "key", ty := .address }]
      returnType := some .uint256
      body := [
        Stmt.letVar "word" (Expr.mappingWord "arrs" (Expr.param "key") 1),
        Stmt.return (Expr.localVar "word")
      ] },
    { name := "setElem"
      params := [
        { name := "key", ty := .address },
        { name := "value", ty := .uint256 }
      ]
      returnType := none
      body := [
        Stmt.setMappingWord "arrs" (Expr.param "key") 1 (Expr.param "value"),
        Stmt.stop
      ] }
  ]
}

/-- Same field, but element index 4 on a `uint256[4]`: one past the end. -/
private def mappingFixedArrayReadOutOfBoundsSpec : CompilationModel :=
  { mappingFixedArraySpec with
    name := "MappingFixedArrayReadOutOfBounds"
    functions := [
      { name := "getElem"
        params := [{ name := "key", ty := .address }]
        returnType := some .uint256
        body := [
          Stmt.letVar "word" (Expr.mappingWord "arrs" (Expr.param "key") 4),
          Stmt.return (Expr.localVar "word")
        ] }
    ] }

private def mappingFixedArrayWriteOutOfBoundsSpec : CompilationModel :=
  { mappingFixedArraySpec with
    name := "MappingFixedArrayWriteOutOfBounds"
    functions := [
      { name := "setElem"
        params := [
          { name := "key", ty := .address },
          { name := "value", ty := .uint256 }
        ]
        returnType := none
        body := [
          Stmt.setMappingWord "arrs" (Expr.param "key") 4 (Expr.param "value"),
          Stmt.stop
        ] }
    ] }

-- The deep walkers `Stmt.checkRecList`/`Expr.checkRec` are well-founded
-- recursions and do not reduce definitionally, so these regressions pin the
-- bounds gate at the node level; the `#eval!` block below exercises the same
-- rejection end-to-end through `compile`.

/-- The in-range index used by `mappingFixedArraySpec` passes the bounds gate. -/
theorem mappingFixedArray_index_1_accepted :
    checkMappingFixedArrayBound mappingFixedArraySpec.fields
      "Stmt.setMappingWord" "arrs" 1 = Except.ok () := by
  decide

/-- Index 4 on a `uint256[4]` is rejected before any Yul is emitted, on both the
    read and the write path. -/
theorem mappingFixedArray_read_index_4_rejected :
    (validateMappingFixedArrayBoundsInExprNode mappingFixedArraySpec.fields
      (Expr.mappingWord "arrs" (Expr.param "key") 4)).toOption = none := by
  decide

theorem mappingFixedArray_write_index_4_rejected :
    (validateMappingFixedArrayBoundsInStmtNode mappingFixedArraySpec.fields
      (Stmt.setMappingWord "arrs" (Expr.param "key") 4 (Expr.param "value"))).toOption =
      none := by
  decide

theorem mappingFixedArray_isMapping :
    isMapping mappingFixedArraySpec.fields "arrs" = true := by
  decide

theorem mappingFixedArray_size :
    mappingFixedArraySize mappingFixedArraySpec.fields "arrs" = some 4 := by
  decide

theorem mappingFixedArray_index_1_in_bounds :
    mappingFixedArrayIndexInBounds mappingFixedArraySpec.fields "arrs" 1 = true := by
  decide

theorem mappingFixedArray_index_4_out_of_bounds :
    mappingFixedArrayIndexInBounds mappingFixedArraySpec.fields "arrs" 4 = false := by
  decide

/-! ## Transient fixedArrayUint128 -/

private def transientFixedArraySpec : CompilationModel := {
  name := "TransientFixedArraySmoke"
  fields := [
    { name := "items", ty := .fixedArrayUint128 4, isTransient := true, «slot» := some 0 }
  ]
  «constructor» := none
  functions := [
    { name := "get"
      params := [{ name := "idx", ty := .uint256 }]
      returnType := some .uint256
      body := [
        Stmt.letVar "word" (Expr.storageArrayElement "items" (Expr.param "idx")),
        Stmt.return (Expr.localVar "word")
      ] },
    { name := "set"
      params := [
        { name := "idx", ty := .uint256 },
        { name := "value", ty := .uint256 }
      ]
      returnType := none
      body := [
        Stmt.setStorageArrayElement "items" (Expr.param "idx") (Expr.param "value"),
        Stmt.stop
      ] }
  ]
}

private def transientItemsField : Field :=
  { name := "items", ty := .fixedArrayUint128 4, isTransient := true, «slot» := some 0 }

theorem transientFixedArray_root_is_transient :
    fieldRootKey transientItemsField 0 = StorageKey.transient 0 :=
  fieldRootKey_transient (f := transientItemsField) (slot := 0) rfl

theorem transientFixedArray_off_persistent_map :
    storageKeySlot (fieldRootKey transientItemsField 0) = none := by
  rw [transientFixedArray_root_is_transient]
  rfl

/-! ## Self-delegate sequence -/

private def selfAddr : Address := (7 : Address)

private def selfWorld : MultiWorld :=
  { accounts := [accountAt selfAddr 0] }

private def selfSite (siteId : Nat) (payload : List Nat) : CallSite :=
  { siteId := siteId
    kind := .delegatecall
    target := selfAddr.toNat
    value := 0
    calldata := payload
    gas := 100 }

private def succeedBody (frame : CallFrame) : CalleeExecution :=
  { result := .success [1], post := frame.calleeEntry }

private def revertBody (frame : CallFrame) : CalleeExecution :=
  { result := .revert [0xde, 0xad], post := frame.calleeEntry }

theorem selfDelegate_two_success_shares_world :
    (denoteSelfDelegateCalls selfWorld selfAddr
      [selfSite 0 [1], selfSite 1 [2]] succeedBody).control =
      SelfDelegateControl.success := by
  decide

theorem selfDelegate_revert_control :
    (denoteSelfDelegateCalls selfWorld selfAddr [selfSite 0 [1]] revertBody).control =
      SelfDelegateControl.callFailed 0 (.revert [0xde, 0xad]) := by
  decide

/-- `selfAddr` mid-execution: entered by `outerSender` carrying 5 wei. -/
private def outerSender : Address := (0x1234 : Address)

private def selfFrameWorld : MultiWorld :=
  { accounts :=
      [{ address := selfAddr
         state :=
           { defaultState with
               thisAddress := selfAddr, sender := outerSender, msgValue := 5 } }] }

/-- DELEGATECALL runs in the caller's frame: the entry state keeps the current
    `msg.sender` and `msg.value` and only pins `address(this)`. -/
theorem selfDelegate_entry_preserves_frame_context :
    ((selfDelegateEntry selfFrameWorld selfAddr (selfSite 0 [1])).map fun frame =>
        (frame.calleeEntry.sender, frame.calleeEntry.msgValue, frame.calleeEntry.thisAddress)) =
      some (outerSender, 5, selfAddr) := by
  decide

/-- Every step of a self-delegate sequence inherits that same frame context. -/
theorem selfDelegate_sequence_preserves_frame_context :
    ((denoteSelfDelegateCalls selfFrameWorld selfAddr
        [selfSite 0 [1], selfSite 1 [2]] succeedBody).calls.map fun observation =>
        (observation.frame.calleeEntry.sender, observation.frame.calleeEntry.msgValue)) =
      [(outerSender, 5), (outerSender, 5)] := by
  decide

#eval! do
  -- FixedArray-under-mapping: mapping(address => uint256[4]) element 1.
  let mappingYul ←
    expectCompileToYul "mapping-fixed-array spec compiles" mappingFixedArraySpec
  expectTrue "mapping-fixed-array read uses mappingSlot + add(index)"
    (contains mappingYul "mappingSlot" && contains mappingYul "add(" )
  expectTrue "mapping-fixed-array write uses sstore at derived slot"
    (contains mappingYul "sstore(")
  expectTrue "mapping-fixed-array index 1 is in bounds"
    (mappingFixedArrayIndexInBounds mappingFixedArraySpec.fields "arrs" 1)
  expectTrue "mapping-fixed-array index 4 is out of bounds"
    (!mappingFixedArrayIndexInBounds mappingFixedArraySpec.fields "arrs" 4)
  expectCompileErrorContains "mapping-fixed-array read at index 4 is rejected"
    mappingFixedArrayReadOutOfBoundsSpec "uses element index 4"
  expectCompileErrorContains "mapping-fixed-array write at index 4 is rejected"
    mappingFixedArrayWriteOutOfBoundsSpec "uses element index 4"
  -- CodeData / SSTORE2: empty, short, dynamic; STOP prefix; read offset 1.
  expectTrue "SSTORE2 prefix is one STOP byte" (sstore2PrefixBytes == 1)
  expectTrue "SSTORE2 read offset is 1"
    (match sstore2PrefixOffset with | .lit 1 => true | _ => false)
  let emptyWrite : CodeDataWrite :=
    { salt := YulExpr.ident "salt", payload := layout [] }
  let emptyRead : CodeDataRead :=
    { pointer := YulExpr.ident "ptr"
      destOffset := YulExpr.ident "dest"
      codeOffset := YulExpr.lit 1
      size := YulExpr.lit 0
      payload := layout [] }
  let emptyRt ←
    match roundtripShape "emptyPtr" "empty" emptyWrite emptyRead with
    | .ok stmts => pure stmts
    | .error err => throw (IO.userError s!"empty CodeData: {err}")
  expectTrue "empty CodeData writes STOP prefix"
    (emptyRt.any fun
      | .exprStmt (.call "mstore8" [_, .lit 0]) => true
      | _ => false)
  expectTrue "empty CodeData read uses extcodecopy at offset 1"
    (emptyRt.any fun
      | .exprStmt (.call "extcodecopy" [_, _, .lit 1, _]) => true
      | _ => false)
  let shortWrite : CodeDataWrite :=
    { salt := YulExpr.ident "salt"
      payload := layout [{ name := "word", ty := .uint256, source := .memory }] }
  let shortRt ←
    match writeTyped "shortPtr" "short" shortWrite with
    | .ok stmts => pure stmts
    | .error err => throw (IO.userError s!"short CodeData: {err}")
  expectTrue "short CodeData writes STOP prefix"
    (shortRt.any fun
      | .exprStmt (.call "mstore8" [_, .lit 0]) => true
      | _ => false)
  let dynamicWrite : CodeDataWrite :=
    { salt := YulExpr.ident "salt"
      payload := runtimeSizedLayout
        [{ name := "market", ty := .tuple [.address], source := .memory,
           sourceBase := "marketAbi" }]
        (YulExpr.ident "marketSize") }
  let dynamicRt ←
    match writeTyped "dynPtr" "dyn" dynamicWrite with
    | .ok stmts => pure stmts
    | .error err => throw (IO.userError s!"dynamic CodeData: {err}")
  expectTrue "dynamic CodeData writes STOP prefix"
    (dynamicRt.any fun
      | .exprStmt (.call "mstore8" [_, .lit 0]) => true
      | _ => false)
  expectTrue "dynamic CodeData create2 uses runtime size plus prefix"
    (dynamicRt.any fun
      | .let_ _ (.call "create2" [_, _, .call "add" [.lit 1, .ident "marketSize"], _]) => true
      | _ => false)
  -- Transient packed fixed array: tload/tstore, off persistent slot map.
  let transientYul ←
    expectCompileToYul "transient fixedArrayUint128 spec compiles" transientFixedArraySpec
  expectTrue "transient fixedArrayUint128 read uses tload"
    (contains transientYul "tload(")
  expectTrue "transient fixedArrayUint128 write uses tstore"
    (contains transientYul "tstore(")
  expectTrue "transient fixedArrayUint128 read helper is the tload helper"
    (contains transientYul "storage_array_index_access_uint128_transient")
  expectTrue "transient fieldRootKey stays off persistent storageKeySlot"
    (storageKeySlot (fieldRootKey transientItemsField 0) == none)
  IO.println "ok: four-features increment"

end Compiler.FourFeaturesTest
