import Compiler.SolidityImport.Import
import Compiler.SolidityImport.Differential

namespace SolidityImportSmoke.SyntheticNestedMappingChecks
open Compiler.CompilationModel

/-! Two-level nested mapping members of storage structs reached through a state variable, a
1-key and a 2-key mapping. Leaf slots and words were observed on anvil with the pinned
solc 0.8.34 (via-IR, osaka, 466 runs); slots use the actual Keccak oracle. -/

solidity_import imported from "Contracts/SolidityImportSmoke" entry "SyntheticNestedMapping.sol"
  using { evmVersion := "osaka", viaIR := true, optimizerRuns := some 466, bytecodeHash := "none" }
  contract SyntheticNestedMapping
  function setAllowance(address,address,uint256,uint256)
  function allowanceOf(address,address,uint256)
  function approve(address,uint256,address,bool)
  function isApproved(address,uint256,address)
  function bumpPacked(address,bytes32,uint8,uint32)
  function clearAllowance(address,address,uint256)

private def run (name : String) (args : List Nat) (storage : Nat → Nat := fun _ => 0) :
    Option Denote.DenoteResult := do
  let f ← imported.model.functions.find? (·.name == name)
  return Denote.denoteFunction SolidityImport.Differential.oracle imported.model f
    { sender := 1, functionSelector := 0, args }
    (Verity.defaultState.withStorageWords fun
      | .slot i => Verity.Core.Uint256.ofNat (storage i)
      | _ => 0)

private def owner : Nat := 0x11
private def spender : Nat := 0x22
private def operator : Nat := 0x33

/-- `accounts[0x11]` base slot (`nonce`), and the leaves `accounts[0x11].allowance[0x22][3]`,
`single.allowance[0x22][3]`, `pairs[bytes32(3)][0x11].allowance[0x22][3]`,
`accounts[0x11].approved[4][0x33]` and `accounts[0x11].packed[0xaa][9]`. -/
private def accountBase : Nat :=
  81814802828211110902652148822845607492490164102093704592762988094020543696735
private def mappedLeaf : Nat :=
  17592646418926061280660426325087383219032545031505721487222878300004870313339
private def singleLeaf : Nat :=
  51566452032361173708226335361823260077299702523971843326129272586565784235042
private def pairLeaf : Nat :=
  90099129337495629151485284816723376181053225323944299079502370985959114233613
private def approvedLeaf : Nat :=
  77575201898202809865887745971660093669844607619846659856201386072482439629386
private def packedLeaf : Nat :=
  95268609511035588137661790072195042957929453673835763403853685598854084948745

#guard match run "setAllowance" [owner, spender, 3, 100] with
  | some w =>
      w.success && w.finalStorage mappedLeaf == 100 && w.finalStorage singleLeaf == 101 &&
      w.finalStorage pairLeaf == 102 && w.finalStorage accountBase == 1 &&
      (match run "allowanceOf" [owner, spender, 3] w.finalStorage with
        | some r => r.success && r.returnWords == [100, 101, 102, 1]
        | none => false) &&
      -- Other keys read zero.
      (match run "allowanceOf" [owner, spender, 4] w.finalStorage with
        | some r => r.success && r.returnWords == [0, 0, 0, 1]
        | none => false) &&
      (match run "clearAllowance" [owner, spender, 3] w.finalStorage with
        | some c => c.success && c.finalStorage mappedLeaf == 0 && c.finalStorage singleLeaf == 101
        | none => false)
  | none => false

#guard match run "approve" [owner, 4, operator, 1] with
  | some w =>
      w.success && w.finalStorage approvedLeaf == 1 &&
      (match run "isApproved" [owner, 4, operator] w.finalStorage with
        | some r => r.success && r.returnWords == [1]
        | none => false) &&
      (match run "isApproved" [owner, 4, operator + 1] w.finalStorage with
        | some r => r.success && r.returnWords == [0]
        | none => false)
  | none => false

-- A packed `uint32` leaf: checked compound assignment, then the 0x11 overflow panic.
#guard match run "bumpPacked" [owner, 0xaa, 9, 2 ^ 32 - 1] with
  | some w =>
      w.success && w.finalStorage packedLeaf == 2 ^ 32 - 1 && w.returnWords == [2 ^ 32 - 1] &&
      (match run "bumpPacked" [owner, 0xaa, 9, 1] w.finalStorage with
        | some r => !r.success
        | none => false)
  | none => false

-- Three-level members and enum inner keys fail closed.
/--
error: SyntheticNestedMapping.sol:72:16: MemberAccess: [solidity-import:unsupported] member deep is opaque in this slice
closure: SyntheticNestedMappingUnsupported.readDeep
deeps[a].deep
-/
#guard_msgs in
solidity_import deep from "Contracts/SolidityImportSmoke" entry "SyntheticNestedMapping.sol"
  using { evmVersion := "osaka", viaIR := true, optimizerRuns := some 466, bytecodeHash := "none" }
  contract SyntheticNestedMappingUnsupported
  function readDeep(address,uint256,uint256)

/--
error: SyntheticNestedMapping.sol:76:16: MemberAccess: [solidity-import:unsupported] member byKind is opaque in this slice
closure: SyntheticNestedMappingUnsupported.readByKind
deeps[a].byKind
-/
#guard_msgs in
solidity_import byKind from "Contracts/SolidityImportSmoke" entry "SyntheticNestedMapping.sol"
  using { evmVersion := "osaka", viaIR := true, optimizerRuns := some 466, bytecodeHash := "none" }
  contract SyntheticNestedMappingUnsupported
  function readByKind(address)

-- The inner mapping `deeps[a].plain[a]` (one key applied) is a full-word mapping at
-- keccak256(a . memberSlot), so it passes as a `mapping(uint256 => uint256) storage` argument.
solidity_import passInner from "Contracts/SolidityImportSmoke" entry "SyntheticNestedMapping.sol"
  using { evmVersion := "osaka", viaIR := true, optimizerRuns := some 466, bytecodeHash := "none" }
  contract SyntheticNestedMappingUnsupported
  function passInner(address)

/-- Leaves `deeps[0x11].plain[0x11][0]` and `[1]`. -/
private def innerLeaf0 : Nat :=
  48605702838723592619221354062932268511991140677690322177052597886465409640914
private def innerLeaf1 : Nat :=
  87285475358389758251347175248435775188584259074750330498380871270369278638488

#guard match passInner.model.functions.find? (·.name == "passInner") with
  | some f =>
      let r := Denote.denoteFunction SolidityImport.Differential.oracle passInner.model f
        { sender := 1, functionSelector := 0, args := [owner] }
        (Verity.defaultState.withStorageWords fun
          | .slot i => Verity.Core.Uint256.ofNat
              (if i == innerLeaf0 then 40 else if i == innerLeaf1 then 2 else 0)
          | _ => 0)
      r.success && r.returnWords == [42]
  | none => false

end SolidityImportSmoke.SyntheticNestedMappingChecks
