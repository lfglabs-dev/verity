import Compiler.SolidityImport.Import
import Compiler.SolidityImport.Differential

/-!
Compile-time checks for `linkedLibrariesMatchSource` (`#2728`) on `LinkedLibraryCallSequence.sol`:
1. Per-root `FunctionStatus.linkedLibraryCalls` and `report.toText` lines, including nested
   linked calls (`bumpPacked` reaches `LinkedCounterLib.bumpPacked` and `LinkedPackLib.pack`,
   excluding the internal `LinkedCounterLib.bump` call) and empty lists on non-calling roots.
2. Per-root `.assumed` local obligation `solidity_linked_library_matches_source` iff the root
   makes an admitted linked library call.
3. Inclusion of `linkedLibrariesMatchSource` in `sourceDigest` when set.
4. Independent verification of entry ABI cleaning (`bindHelperParams` on a `void` linked call vs
   an `internal` call) and single/multi-return ABI cleaning (`inlineFn` / `inlineMultiFn` on
   the legacy pipeline where `uint8(raw)`, `address(uint160(raw))` and `bytes4(raw)` leave
   uncleaned words inside the library body).
-/
namespace SolidityImportSmoke.LinkedLibraryCallChecks

open Compiler Compiler.CompilationModel

solidity_import withLinked from "Contracts/SolidityImportSmoke" entry "LinkedLibraryCallSequence.sol"
  using { evmVersion := "osaka", viaIR := true, optimizerRuns := some 466, bytecodeHash := "none",
          linkedLibrariesMatchSource := true }
  contract LinkedLibraryCallFixture
  function setConfig(bytes32,address,Mode)
  function bumpPacked(bytes32,uint256,address)
  function addExternal(bytes32,uint256)
  function cleanNarrow(uint256,uint256,uint256,uint256,uint256,uint256)
  function cleanReturnFromWide(uint256,uint256,bytes32)
  function entryCleanVoid(bytes32,uint256,uint256,uint256)
  function internalRawVoid(bytes32,uint256,uint256,uint256)
  function roundTripBytesIsolation(bytes,bytes1,bytes1,uint8)
  function duplicateDisjoint(uint8,uint8,bytes1)
  function nestedBytesAndStorage(bytes32,bytes,uint256,uint256,bytes1)
  function inspectCode(bytes32,uint256,uint256)
  function word(bytes32)
  function total(bytes32)

solidity_import withLinkedWordsOnly from "Contracts/SolidityImportSmoke" entry "LinkedLibraryCallSequence.sol"
  using { evmVersion := "osaka", viaIR := true, optimizerRuns := some 466, bytecodeHash := "none",
          linkedLibrariesMatchSource := true }
  contract LinkedLibraryCallFixture
  function word(bytes32)
  function total(bytes32)

solidity_import withoutLinkedWordsOnly from "Contracts/SolidityImportSmoke" entry "LinkedLibraryCallSequence.sol"
  using { evmVersion := "osaka", viaIR := true, optimizerRuns := some 466, bytecodeHash := "none",
          linkedLibrariesMatchSource := false }
  contract LinkedLibraryCallFixture
  function word(bytes32)
  function total(bytes32)

solidity_import legacyLinked from "Contracts/SolidityImportSmoke" entry "LinkedLibraryCallSequence.sol"
  using { evmVersion := "osaka", viaIR := false, optimizerRuns := some 466, bytecodeHash := "none",
          linkedLibrariesMatchSource := true }
  contract LinkedLibraryCallFixture
  function cleanReturnFromWide(uint256,uint256,bytes32)
  function roundTripBytesIsolation(bytes,bytes1,bytes1,uint8)
  function duplicateDisjoint(uint8,uint8,bytes1)

private def has (text needle : String) : Bool := (text.splitOn needle).length > 1

-- (a) Per-root linked library call report entries and rendered text.
#guard withLinked.report.functions.map (fun st =>
    (st.function, st.linkedLibraryCalls.map fun u => (u.library, u.function, u.file))) ==
  [("setConfig", [("LinkedPackLib", "pack", "LinkedLibraryCallSequence.sol")]),
   ("bumpPacked", [("LinkedCounterLib", "bumpPacked", "LinkedLibraryCallSequence.sol"),
                   ("LinkedPackLib", "pack", "LinkedLibraryCallSequence.sol")]),
   ("addExternal", [("LinkedCounterLib", "addAmount", "LinkedLibraryCallSequence.sol")]),
   ("cleanNarrow",
    [("LinkedPackLib", "passUint8", "LinkedLibraryCallSequence.sol"),
     ("LinkedPackLib", "roundTripNarrow", "LinkedLibraryCallSequence.sol")]),
   ("cleanReturnFromWide",
    [("LinkedPackLib", "narrowSingleFromWide", "LinkedLibraryCallSequence.sol"),
     ("LinkedPackLib", "narrowMultiFromWide", "LinkedLibraryCallSequence.sol")]),
   ("entryCleanVoid", [("LinkedCounterLib", "sinkNarrow", "LinkedLibraryCallSequence.sol")]),
   ("internalRawVoid", []),
   ("roundTripBytesIsolation", [("LinkedPackLib", "mutateAndTag", "LinkedLibraryCallSequence.sol")]),
   ("duplicateDisjoint", [("LinkedPackLib", "duplicateShared", "LinkedLibraryCallSequence.sol")]),
   ("nestedBytesAndStorage",
    [("LinkedCounterLib", "recordDigest", "LinkedLibraryCallSequence.sol"),
     ("LinkedPackLib", "mutateAndTag", "LinkedLibraryCallSequence.sol"),
     ("LinkedPackLib", "mutateAndTag", "LinkedLibraryCallSequence.sol")]),
   ("inspectCode",
    [("LinkedPackLib", "probeCodeSize", "LinkedLibraryCallSequence.sol"),
     ("LinkedPackLib", "classifyAccountCode", "LinkedLibraryCallSequence.sol")]),
   ("word", []),
   ("total", [])]

#guard has withLinked.report.toText "\n  linked library LinkedCounterLib.bumpPacked decl "
#guard has withLinked.report.toText "\n  linked library LinkedPackLib.pack decl "
#guard has withLinked.report.toText "\n  linked library LinkedCounterLib.recordDigest decl "
#guard has withLinked.report.toText "\n  linked library LinkedPackLib.mutateAndTag decl "
#guard !has withLinked.report.toText "\n  linked library LinkedCounterLib.bump "

-- (b) `.assumed` `solidity_linked_library_matches_source` obligation surfaced iff a root
-- relies on a linked library call.
#guard withLinked.model.functions.map (fun f =>
    (f.name, (f.localObligations.filter (·.name == "solidity_linked_library_matches_source")).map
      fun o => (o.name, o.proofStatus))) ==
  [("setConfig", [("solidity_linked_library_matches_source", .assumed)]),
   ("bumpPacked", [("solidity_linked_library_matches_source", .assumed)]),
   ("addExternal", [("solidity_linked_library_matches_source", .assumed)]),
   ("cleanNarrow", [("solidity_linked_library_matches_source", .assumed)]),
   ("cleanReturnFromWide", [("solidity_linked_library_matches_source", .assumed)]),
   ("entryCleanVoid", [("solidity_linked_library_matches_source", .assumed)]),
   ("internalRawVoid", []),
   ("roundTripBytesIsolation", [("solidity_linked_library_matches_source", .assumed)]),
   ("duplicateDisjoint", [("solidity_linked_library_matches_source", .assumed)]),
   ("nestedBytesAndStorage", [("solidity_linked_library_matches_source", .assumed)]),
   ("inspectCode", [("solidity_linked_library_matches_source", .assumed)]),
   ("word", []),
   ("total", [])]

-- (c) `linkedLibrariesMatchSource` is included in `sourceDigest` when set.
#guard withLinkedWordsOnly.report.sourceDigest != withoutLinkedWordsOnly.report.sourceDigest

-- (d) Entry cleaning (`bindHelperParams`) on a void linked call vs an internal call, and
-- single/multi-return cleaning (`inlineFn` / `inlineMultiFn`) on legacy wide-input helpers.
private def exprHasMask (mask : Nat) : Expr → Bool
  | .bitAnd a (.literal m) => m == mask || exprHasMask mask a
  | .bitAnd a b | .bitOr a b | .bitXor a b | .add a b | .sub a b | .mul a b
  | .div a b | .mod a b | .shl a b | .shr a b | .eq a b | .lt a b | .gt a b
  | .le a b | .ge a b => exprHasMask mask a || exprHasMask mask b
  | .bitNot a | .logicalNot a | .mload a | .calldataload a => exprHasMask mask a
  | .signextend a b => exprHasMask mask a || exprHasMask mask b
  | .keccak256 a b => exprHasMask mask a || exprHasMask mask b
  | _ => false

private def stmtHasMask (fuel mask : Nat) (s : Stmt) : Bool :=
  match fuel, s with
  | 0, _ => false
  | _ + 1, .letVar _ e | _ + 1, .assignVar _ e => exprHasMask mask e
  | k + 1, .ite c t f =>
      exprHasMask mask c || t.any (stmtHasMask k mask) || f.any (stmtHasMask k mask)
  | k + 1, .forEach _ n b => exprHasMask mask n || b.any (stmtHasMask k mask)
  | _ + 1, _ => false

private def bodyHasMask (model : CompilationModel) (name : String) (mask : Nat) : Bool :=
  match model.functions.find? (·.name == name) with
  | none => false
  | some f => f.body.any (stmtHasMask 64 mask)

#guard bodyHasMask withLinked.model "entryCleanVoid" 255
#guard bodyHasMask withLinked.model "entryCleanVoid" (2 ^ 160 - 1)
#guard bodyHasMask withLinked.model "entryCleanVoid" ((2 ^ 32 - 1) * 2 ^ 224)
#guard !bodyHasMask withLinked.model "internalRawVoid" 255
#guard !bodyHasMask withLinked.model "internalRawVoid" (2 ^ 160 - 1)
#guard !bodyHasMask withLinked.model "internalRawVoid" ((2 ^ 32 - 1) * 2 ^ 224)

private def observesWords (model : CompilationModel) (name : String) (args words : List Nat) : Bool :=
  match model.functions.find? (·.name == name) with
  | none => false
  | some f =>
    let r := Denote.denoteFunction SolidityImport.Differential.oracle model f
      { sender := 1, functionSelector := 0, args } Verity.defaultState
    r.success && r.returnWords == words

#guard observesWords withLinked.model "cleanNarrow"
  [0x105, 0x1ff, 2, 0x207, 2 ^ 160 + 0x42, 0x11223344 * 2 ^ 224 + 0x99]
  [5, 2 ^ 256 - 1, 1, 7, 0x42, 0x11223344 * 2 ^ 224]

#guard observesWords legacyLinked.model "cleanReturnFromWide"
  [0x105, 2 ^ 160 + 0x42, 0x11223344 * 2 ^ 224 + 0x99]
  [5, 0x42, 0x11223344 * 2 ^ 224]

-- (e) Copy-in isolation and copy-out disjointness on `bytes memory` across via-IR and legacy:
-- `duplicateDisjoint(0x22, 0, 0x99)` mutates `first[0] := 0x99`; `second[0]` stays `0x22`.
private def observesPrefix (model : CompilationModel) (name : String) (args prefixWords : List Nat) : Bool :=
  match model.functions.find? (·.name == name) with
  | none => false
  | some f =>
    let r := Denote.denoteFunction SolidityImport.Differential.oracle model f
      { sender := 1, functionSelector := 0, args } Verity.defaultState
    r.success && r.returnWords.take prefixWords.length == prefixWords

#guard observesPrefix withLinked.model "duplicateDisjoint" [0x22, 0, 0x99 * 2 ^ 248] [0x99, 0x22]
#guard observesPrefix legacyLinked.model "duplicateDisjoint" [0x22, 0, 0x99 * 2 ^ 248] [0x99, 0x22]
#guard observesPrefix withLinked.model "roundTripBytesIsolation"
  [128, 0xff * 2 ^ 248, 0xaa * 2 ^ 248, 0x77, 2, 0x1122 * 2 ^ 240]
  [0x11, 0x22, 0x11, 0xaa, 0x77]
#guard observesPrefix legacyLinked.model "roundTripBytesIsolation"
  [128, 0xff * 2 ^ 248, 0xaa * 2 ^ 248, 0x77, 2, 0x1122 * 2 ^ 240]
  [0x11, 0x22, 0x11, 0xaa, 0x77]

-- (f) Frame-neutral `extcodesize` inline assembly inside direct and nested internal
-- linked-library calls (deployed contract vs empty account, dirty upper address bits,
-- and caller-shadowed named return variable `size`).
private def observesWithForeignCode (model : CompilationModel) (name : String)
    (foreignAddr : Nat) (foreignBytes : List (Fin 256)) (args words : List Nat) : Bool :=
  match model.functions.find? (·.name == name) with
  | none => false
  | some f =>
    let addr := Verity.Core.Address.ofNat foreignAddr
    let s0 := Verity.defaultState
    let s1 := s0.writeAccount addr { s0.accountWorld addr with code := foreignBytes }
    let r := Denote.denoteFunction SolidityImport.Differential.oracle model f
      { sender := 1, functionSelector := 0, args } s1
    r.success && r.returnWords == words

#guard observesWithForeignCode withLinked.model "inspectCode"
  0x42 [0, 17, 34] [9, 2 ^ 160 + 0x42, 5] [3, 3, 8 * 2 ^ 16]
#guard observesWithForeignCode withLinked.model "inspectCode"
  0x42 [] [9, 0x99, 5] [0, 0, 5 * 2 ^ 16 + 0x101]

theorem witness_linked_library_frame_neutral_excludes_address :
    let szDecl := Lean.Json.mkObj [("nodeType", .str "VariableDeclaration"), ("id", .num 2),
      ("name", .str "size"), ("stateVariable", .bool false), ("constant", .bool false),
      ("mutability", .str "mutable"), ("storageLocation", .str "default"),
      ("typeDescriptions", Lean.Json.mkObj [("typeIdentifier", .str "t_uint256")])]
    let fn := Lean.Json.mkObj [("nodeType", .str "FunctionDefinition"),
      ("parameters", Lean.Json.mkObj [("parameters", .arr #[])]),
      ("body", Lean.Json.mkObj [("statements", .arr #[szDecl])])]
    let ref2 := Lean.Json.mkObj [("declaration", .num 2), ("isOffset", .bool false),
      ("isSlot", .bool false), ("valueSize", .num 1), ("src", .str "a")]
    let lhs := Lean.Json.mkObj [("nodeType", .str "YulIdentifier"), ("name", .str "size"),
      ("src", .str "a")]
    let rhsAddr := Lean.Json.mkObj [("nodeType", .str "YulFunctionCall"),
      ("functionName", Lean.Json.mkObj [("nodeType", .str "YulIdentifier"),
        ("name", .str "address")]),
      ("arguments", .arr #[])]
    let asmAddr := Lean.Json.mkObj [("nodeType", .str "InlineAssembly"),
      ("externalReferences", .arr #[ref2]),
      ("AST", Lean.Json.mkObj [("nodeType", .str "YulBlock"),
        ("statements", .arr #[Lean.Json.mkObj [("nodeType", .str "YulAssignment"),
          ("variableNames", .arr #[lhs]), ("value", rhsAddr)]])])]
    SolidityImport.linkedLibraryFrameNeutralBuiltinArity? "address" = none ∧
    SolidityImport.isLinkedLibraryFrameNeutralInlineAssembly fn asmAddr 8 = false := by
  decide

end SolidityImportSmoke.LinkedLibraryCallChecks
