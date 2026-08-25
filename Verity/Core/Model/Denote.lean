import Verity.Core
import Verity.Core.Uint256
import Verity.Core.Int256
import Verity.Core.Model.Constants
import Verity.Core.Model.DynamicAbi
import Verity.Core.Model.Types


/-!
# Compiler-Free Denotation of the Deep Compilation Model (P2, one-AST refactor)

This module is the **canonical denotation** of the deep embedding in
`Verity.Core.Model.Types` (`Compiler.CompilationModel.Expr` / `Stmt` /
`FunctionSpec` / `CompilationModel`). It interprets a `FunctionSpec` directly
over `Verity.ContractState`, with no dependency on any `Compiler.*` module, so
that the executable shallow program can eventually be *derived* from the deep
model instead of being dual-emitted by the contract macro.

`Compiler.Proofs.IRGeneration.SourceSemantics` is currently the
proven-against-IR semantics. This file mirrors it decision-for-decision
(`evalExpr`, `evalExprList`, `execStmt`/`execStmtList`/`execForEachLoop`,
the storage read/write helpers, and `interpretFunction`), and the planned
`denote_eq_sourceSemantics` equivalence (P4) will make this the single
semantic definition.

## Intentional differences from `SourceSemantics`

1. **Oracle parameterization.** `SourceSemantics` reaches into compiler-only
   engines for two operations; here they are routed through a `DenoteOracle`
   structure that the proof layer instantiates with the real engines:
   - `mappingSlot` — `Compiler.Proofs.abstractMappingSlot` /
     `solidityMappingSlot` (`keccak256(abi.encode(key, baseSlot))`).
   - `keccakMemorySlice` — `SourceSemantics.keccakMemorySlice`
     (Keccak-256 of a word-aligned memory slice, for `Expr.keccak256`).
   Everything else (`calldataloadWord`, packed-bits masks, slot alias
   expansion, word normalization) is pure arithmetic and is replicated
   locally, byte-for-byte faithful to the originals.
2. **Event-less statement semantics only.** This file mirrors the event-less
   `execStmt`/`execStmtList` variants (not `execStmtWithEvents`): the
   `Stmt.emit` arm appends a `Verity.Event` whose `indexedArgs` are empty and
   whose data args are the raw resolved words — exactly
   `SourceSemantics.execStmt`'s `.emit` arm (which invokes the event helpers
   with an empty `EventDef` list). Consequently `denoteFunction` matches
   `SourceSemantics.interpretFunction` for specs whose event declarations do
   not affect encoding (in particular for `spec.events = []`); declared-event
   topic/scratch-memory modelling stays in the proof layer for now.
3. **Mutable word-array memory.** Memory-backed `uint256[]` locals use the
   compiler's paired `<name>_data_offset` / `<name>_length` bindings. Length
   and checked element reads are denoted against `ContractState.memory`, so
   preceding `mstore` statements (including `setMemoryArrayElement`) are
   observable to later reads and bounded loops.
4. **Mapping write storage view.** `SourceSemantics` threads address/uint
   keyed mapping writes through the proof-layer `IRStorageSlot`/`IRStorageWord`
   wrappers (which are `UInt256` with `2^256` modulus). Here the same fold is
   expressed directly on word-normalized `Nat` slots; the two are extensionally
   equal because `IRStorageSlot.ofNat`/`toNat` round-trip is `· % 2^256`.

## Outside the initial denotation fragment

Exactly the constructs `SourceSemantics` itself maps to `none`/`.revert`, apart
from the memory-backed word arrays intentionally widened here:
`arrayElementDynamic*`, `paramDynamic*`, `forkIfAtLeast`, `mappingChain`
reads with zero or three-plus keys (one/two-key reads and writes are
supported), and every `Expr`/`Stmt` constructor not listed
in the arms below (raw calls, ABI re-encoding returns, ECM, unsafe Yul,
`matchAdt`, internal calls — internal-call semantics live in the separate
`*WithHelpers` interpreters and are not part of this fragment).
-/
namespace Compiler.CompilationModel.Denote

open Compiler.CompilationModel

/-! ## Word-level helpers (mirroring `SourceSemantics`) -/

def wordNormalize (n : Nat) : Nat :=
  ((n : Verity.Core.Uint256) : Nat)

def uint8Modulus : Nat := 2 ^ 8

def boolWord (b : Bool) : Nat :=
  if b then 1 else 0

/-- Mirrors `Compiler.CompilationModel.packedMaskNat` (ValidationHelpers). -/
def packedMaskNat (packed : PackedBits) : Nat :=
  if packed.width >= 256 then
    Compiler.Constants.evmModulus - 1
  else
    (2 ^ packed.width) - 1

/-- Mirrors `Compiler.CompilationModel.packedBitsValid` (ValidationHelpers). -/
def packedBitsValid (packed : PackedBits) : Bool :=
  packed.width > 0 &&
  packed.width <= 256 &&
  packed.offset < 256 &&
  packed.offset + packed.width <= 256

/-- Mirrors `Compiler.Proofs.YulGeneration.selectorWord`. -/
def selectorWord (selector : Nat) : Nat :=
  (selector % Compiler.Constants.selectorModulus) * (2 ^ Compiler.Constants.selectorShift)

/-- Mirrors `Compiler.Proofs.YulGeneration.calldataloadWord` (pure arithmetic). -/
def calldataloadWord (selector : Nat) (calldata : List Nat) (offset : Nat) : Nat :=
  if offset = 0 then
    selectorWord selector
  else if offset < 4 then
    0
  else
    let p := offset - 4
    let q := p / 32
    let r := p % 32
    if r = 0 then
      calldata.getD q 0 % Compiler.Constants.evmModulus
    else
      let hi := calldata.getD q 0 % Compiler.Constants.evmModulus
      let lo := calldata.getD (q + 1) 0 % Compiler.Constants.evmModulus
      ((hi % (2 ^ (8 * (32 - r)))) * (2 ^ (8 * r)) + lo / (2 ^ (8 * (32 - r)))) %
        Compiler.Constants.evmModulus

/-- Mirrors `Compiler.Proofs.YulGeneration.calldatacopyWritesAt`. -/
def calldatacopyWritesAt (dst size offset : Nat) : Prop :=
  dst ≤ offset ∧ offset < dst + 32 * (size / 32) ∧ (offset - dst) % 32 = 0

instance (dst size offset : Nat) : Decidable (calldatacopyWritesAt dst size offset) := by
  unfold calldatacopyWritesAt; infer_instance

/-! ## Slot alias expansion (mirroring `Compiler.CompilationModel.LayoutValidation`) -/

def dedupNatPreserve (xs : List Nat) : List Nat :=
  let rec go (seen : List Nat) : List Nat → List Nat
    | [] => []
    | x :: rest =>
        if seen.contains x then
          go seen rest
        else
          x :: go (x :: seen) rest
  go [] xs

def slotAliasForSource (sourceSlot : Nat) (range : SlotAliasRange) : Option Nat :=
  if range.sourceStart <= sourceSlot && sourceSlot <= range.sourceEnd then
    some (range.targetStart + (sourceSlot - range.sourceStart))
  else
    none

def derivedAliasSlotsForSource (sourceSlot : Nat) (ranges : List SlotAliasRange) : List Nat :=
  dedupNatPreserve (ranges.filterMap (slotAliasForSource sourceSlot))

def applySlotAliasRanges (fields : List Field) (ranges : List SlotAliasRange) : List Field :=
  let rec go (remaining : List Field) (idx : Nat) : List Field :=
    match remaining with
    | [] => []
    | f :: rest =>
        let sourceSlot := f.slot.getD idx
        let derivedAliases := derivedAliasSlotsForSource sourceSlot ranges
        let mergedAliases := dedupNatPreserve (f.aliasSlots ++ derivedAliases)
        ({ f with aliasSlots := mergedAliases } :: go rest (idx + 1))
  go fields 0

def effectiveFields (spec : CompilationModel) : List Field :=
  applySlotAliasRanges spec.fields spec.slotAliasRanges

/-! ## Oracle for compiler-engine dependencies -/

/-- Functions of the denotation that `SourceSemantics` implements with
compiler-only engines. The proof layer instantiates:
- `mappingSlot := Compiler.Proofs.abstractMappingSlot`
  (= `solidityMappingSlot`, i.e. `keccak256(abi.encode(key, baseSlot))`);
- `keccakMemorySlice := SourceSemantics.keccakMemorySlice`
  (Keccak-256 over the word-aligned memory slice `[offset, offset+size)`). -/
structure DenoteOracle where
  /-- Mapping storage slot derivation for base slot and key. -/
  mappingSlot : Nat → Nat → Nat
  /-- `keccak256(offset, size)` over word-addressed memory, as a 256-bit word. -/
  keccakMemorySlice : (Nat → Verity.Core.Uint256) → Nat → Nat → Nat

/-! ## Environment and runtime state -/

/-- Param/local bindings: innermost binding first, lookup by first match. -/
abbrev Env := List (String × Nat)

def bindValue (bindings : Env) (name : String) (value : Nat) : Env :=
  (name, value) :: bindings.filter (fun entry => entry.1 != name)

def bindValues (bindings : Env) : List String → List Nat → Env
  | [], _ => bindings
  | _ :: _, [] => bindings
  | name :: names, value :: values => bindValues (bindValue bindings name value) names values

def lookupValue (bindings : Env) (name : String) : Nat :=
  bindings.find? (fun entry => entry.1 == name) |>.map Prod.snd |>.getD 0

def lookupBinding? (bindings : Env) (name : String) : Option Nat :=
  bindings.find? (fun entry => entry.1 == name) |>.map Prod.snd

/-- Mirrors `SourceSemantics.RuntimeState`. -/
structure DenoteState where
  world : Verity.ContractState
  immutable : String → Verity.Core.Uint256 := fun _ => 0
  bindings : Env
  selector : Nat := 0
  externalCallSucceeded : Nat → Bool := fun _ => false
  externalCallReturnValues : Nat → List Nat := fun _ => []
  externalCallPostWorld : Nat → Option Verity.ContractState := fun _ => none
  externalCallIndex : Nat := 0

/-- Mirrors `SourceSemantics.StmtResult`. -/
inductive StmtOutcome where
  | continue (state : DenoteState)
  | stop (state : DenoteState)
  | return (value : Nat) (state : DenoteState)
  | revert

/-! ## Storage read helpers (mirroring `SourceSemantics`) -/

def fieldUsesAddressStorage (field : Field) : Bool :=
  match field.ty with
  | .address => true
  | _ => false

def fieldUsesDynamicArrayStorage (field : Field) : Bool :=
  match field.ty with
  | .dynamicArray _ => true
  | _ => false

def findResolvedFieldAtStorageSlot (fields : List Field) (isTransient : Bool)
    (slot : Nat) : Option Field :=
  let rec go (remaining : List Field) (idx : Nat) : Option Field :=
    match remaining with
    | [] => none
    | field :: rest =>
        let resolvedSlot := field.slot.getD idx
        if field.isTransient == isTransient &&
            (wordNormalize resolvedSlot = wordNormalize slot ||
            (field.aliasSlots.map wordNormalize).contains (wordNormalize slot)) then
          some field
        else
          go rest (idx + 1)
  go fields 0

def findResolvedFieldAtSlot (fields : List Field) (slot : Nat) : Option Field :=
  findResolvedFieldAtStorageSlot fields false slot

def findDynamicArrayElementAtSlot (oracle : DenoteOracle)
    (fields : List Field) (world : Verity.ContractState) (targetSlot : Nat) : Option Nat :=
  let rec scanElements (baseSlot : Nat) : List Verity.Core.Uint256 → Nat → Option Nat
    | [], _ => none
    | value :: rest, idx =>
        if oracle.mappingSlot baseSlot idx = wordNormalize targetSlot then
          some value.val
        else
          scanElements baseSlot rest (idx + 1)
  let rec go (remaining : List Field) (idx : Nat) : Option Nat :=
    match remaining with
    | [] => none
    | field :: rest =>
        let resolvedSlot := field.slot.getD idx
        match field.ty with
        | .dynamicArray _ =>
            match scanElements resolvedSlot (world.readArray resolvedSlot) 0 with
            | some value => some value
            | none => go rest (idx + 1)
        | _ => go rest (idx + 1)
  go fields 0

def encodeStorageAt (oracle : DenoteOracle)
    (fields : List Field) (world : Verity.ContractState) (slot : Nat) : Nat :=
  match findResolvedFieldAtSlot fields slot with
  | some field =>
      if fieldUsesAddressStorage field then
        (world.readAddrSlot slot).val
      else if fieldUsesDynamicArrayStorage field then
        (world.readArray slot).length
      else
        (world.readSlot slot).val
  | none =>
      match findDynamicArrayElementAtSlot oracle fields world slot with
      | some value => value
      | none => (world.readSlot slot).val

def encodeStorage (oracle : DenoteOracle)
    (spec : CompilationModel) (world : Verity.ContractState) : Nat → Nat :=
  encodeStorageAt oracle (effectiveFields spec) world

/-! ## Storage write helpers (mirroring `SourceSemantics`) -/

def writeUintSlots (world : Verity.ContractState) (slots : List Nat) (value : Nat) :
    Verity.ContractState :=
  let word : Verity.Core.Uint256 := value
  let targets := slots.map wordNormalize
  world.writeSlots targets word

def writeStorageWordSlots (world : Verity.ContractState) (slots : List Nat)
    (wordOffset value : Nat) : Verity.ContractState :=
  let word : Verity.Core.Uint256 := value
  let addr := Verity.wordToAddress word
  let targets := slots.map (fun slot => wordNormalize (slot + wordOffset))
  (world.writeSlots targets word).writeAddrSlots targets addr

def writeAddressSlots (world : Verity.ContractState) (slots : List Nat) (value : Nat) :
    Verity.ContractState :=
  let addr := Verity.wordToAddress (value : Verity.Core.Uint256)
  let targets := slots.map wordNormalize
  world.writeAddrSlots targets addr

def fieldIsTransient (fields : List Field) (name : String) : Bool :=
  match findFieldWithResolvedSlot fields name with
  | some (field, _) => field.isTransient
  | none => false

def readFieldWord (world : Verity.ContractState) (field : Field) (slot : Nat) :
    Verity.Core.Uint256 :=
  if field.isTransient then
    world.readTransient (wordNormalize slot)
  else
    world.readSlot (wordNormalize slot)

def writeTransientTargets (world : Verity.ContractState) (targets : List Nat) (value : Nat) :
    Verity.ContractState :=
  let word : Verity.Core.Uint256 := value
  let targets := targets.map wordNormalize
  world.writeTransientSlots targets word

def packedWordWrite (current value : Nat) (packed : PackedBits) : Nat :=
  let maskNat := packedMaskNat packed
  let shiftedMaskNat := maskNat * (2 ^ packed.offset)
  let packedValue := Verity.Core.Uint256.and value maskNat
  let cleared := Verity.Core.Uint256.and current (Verity.Core.Uint256.not shiftedMaskNat)
  (Verity.Core.Uint256.or cleared (Verity.Core.Uint256.shl packed.offset packedValue)).val

def writeUintFieldSlots (fields : List Field) (fieldName : String)
    (world : Verity.ContractState) (slots : List Nat) (value : Nat) :
    Verity.ContractState :=
  match findFieldWithResolvedSlot fields fieldName with
  | some (field, _) =>
      match field.packedBits with
      | some packed =>
          let targets := slots.map wordNormalize
          if field.isTransient then
            world.modifyTransientSlots targets
              (fun current => packedWordWrite current.val value packed)
          else
            world.modifySlots targets
              (fun current => packedWordWrite current.val value packed)
      | none =>
          if field.isTransient then writeTransientTargets world slots value
          else writeUintSlots world slots value
  | none => writeUintSlots world slots value

def writeStorageWordFieldSlots (fields : List Field) (fieldName : String)
    (world : Verity.ContractState) (slots : List Nat) (wordOffset value : Nat) :
    Verity.ContractState :=
  if fieldIsTransient fields fieldName then
    writeTransientTargets world (slots.map (fun slot => slot + wordOffset)) value
  else
    writeStorageWordSlots world slots wordOffset value

def writeAddressFieldSlots (fields : List Field) (fieldName : String)
    (world : Verity.ContractState) (slots : List Nat) (value : Nat) :
    Verity.ContractState :=
  if fieldIsTransient fields fieldName then
    writeTransientTargets world slots (Verity.wordToAddress (value : Verity.Core.Uint256)).val
  else
    writeAddressSlots world slots value

def writeMappingTargets (fields : List Field) (fieldName : String)
    (world : Verity.ContractState) (targets : List Nat) (value : Nat) :
    Verity.ContractState :=
  if fieldIsTransient fields fieldName then
    writeTransientTargets world targets value
  else
    let word : Verity.Core.Uint256 := value
    world.writeSlots (targets.map wordNormalize) word

/-- Nat-level rendering of `Compiler.Proofs.abstractStoreMappingEntry` over a
word-normalized storage view (see header note 3). -/
def storeMappingEntryNat (oracle : DenoteOracle)
    (storage : Nat → Nat) (baseSlot key value : Nat) : Nat → Nat :=
  fun s =>
    if s = wordNormalize (oracle.mappingSlot baseSlot key) then
      wordNormalize value
    else
      storage s

/-- Word-normalized flat-storage view of the world, the Nat-level analogue of
`SourceSemantics`' `IRStorageSlot → IRStorageWord` round-trip. -/
def storageNatView (world : Verity.ContractState) : Nat → Nat :=
  fun s => (world.readSlot (wordNormalize s)).val

def writeAddressKeyedMappingSlots (oracle : DenoteOracle)
    (world : Verity.ContractState) (slots : List Nat) (key value : Nat) :
    Verity.ContractState :=
  match slots with
  | [] => world
  | slot :: _ =>
      let keyAddr := Verity.wordToAddress (key : Verity.Core.Uint256)
      let word : Verity.Core.Uint256 := value
      let flatStorage :=
        slots.foldl
          (fun current slot => storeMappingEntryNat oracle current slot key value)
          (storageNatView world)
      (world.withStorageChannel
          (fun _ => fun s => ((flatStorage (wordNormalize s) : Verity.Core.Uint256)))).writeMap
        slot keyAddr word

def mappingSlotChain (oracle : DenoteOracle) (baseSlot : Nat) (keys : List Nat) : Nat :=
  keys.foldl oracle.mappingSlot baseSlot

def writeAddressKeyedMappingChainSlots (oracle : DenoteOracle)
    (world : Verity.ContractState) (slots keys : List Nat) (value : Nat) :
    Verity.ContractState :=
  let word : Verity.Core.Uint256 := value
  let targets := slots.map (fun slot => wordNormalize (mappingSlotChain oracle slot keys))
  world.writeSlots targets word

def writeAddressKeyedMappingWordSlots (oracle : DenoteOracle)
    (world : Verity.ContractState) (slots : List Nat) (key wordOffset value : Nat) :
    Verity.ContractState :=
  let word : Verity.Core.Uint256 := value
  let targets :=
    slots.map (fun slot => wordNormalize (oracle.mappingSlot slot key + wordOffset))
  world.writeSlots targets word

def readFixedUint128ArrayElement
    (world : Verity.ContractState) (slot size index : Nat) : Option Nat :=
  if index < size then
    let word := (world.storage (wordNormalize (slot + index / 2))).val
    some (Verity.Core.Uint256.and
      (Verity.Core.Uint256.shr ((index % 2) * 128) word)
      ((2 ^ 128 - 1 : Nat))).val
  else
    none

def writeFixedUint128ArrayElementSlots
    (world : Verity.ContractState) (slots : List Nat) (size index value : Nat) :
    Option Verity.ContractState :=
  if index < size then
    let offset := (index % 2) * 128
    let packed : PackedBits := { offset := offset, width := 128 }
    let targets := slots.map (fun slot => wordNormalize (slot + index / 2))
    some (world.modifySlots targets
      (fun current => packedWordWrite current.val value packed))
  else
    none

def writeAddressKeyedMappingPackedWordSlots (oracle : DenoteOracle)
    (world : Verity.ContractState) (slots : List Nat) (key wordOffset : Nat)
    (packed : PackedBits) (value : Nat) :
    Verity.ContractState :=
  let targets :=
    slots.map (fun slot => wordNormalize (oracle.mappingSlot slot key + wordOffset))
  world.modifySlots targets
    (fun current => packedWordWrite current.val value packed)

def writeAddressKeyedMappingPackedWordFieldSlots (oracle : DenoteOracle)
    (fields : List Field) (fieldName : String)
    (world : Verity.ContractState) (slots : List Nat) (key wordOffset : Nat)
    (packed : PackedBits) (value : Nat) :
    Verity.ContractState :=
  let targets := slots.map (fun slot => wordNormalize (oracle.mappingSlot slot key + wordOffset))
  if fieldIsTransient fields fieldName then
    world.modifyTransientSlots targets
      (fun current => packedWordWrite current.val value packed)
  else
    writeAddressKeyedMappingPackedWordSlots oracle world slots key wordOffset packed value

def writeUintKeyedMappingSlots (oracle : DenoteOracle)
    (world : Verity.ContractState) (slots : List Nat) (key value : Nat) :
    Verity.ContractState :=
  match slots with
  | [] => world
  | slot :: _ =>
      let keyWord : Verity.Core.Uint256 := key
      let word : Verity.Core.Uint256 := value
      let flatStorage :=
        slots.foldl
          (fun current slot => storeMappingEntryNat oracle current slot key value)
          (storageNatView world)
      (world.withStorageChannel
          (fun _ => fun s => ((flatStorage (wordNormalize s) : Verity.Core.Uint256)))).writeMapUint
        slot keyWord word

def writeAddressKeyedMapping2Slots (oracle : DenoteOracle)
    (world : Verity.ContractState) (slots : List Nat) (key1 key2 value : Nat) :
    Verity.ContractState :=
  match slots with
  | [] => world
  | slot :: _ =>
      let key1Addr := Verity.wordToAddress (key1 : Verity.Core.Uint256)
      let key2Addr := Verity.wordToAddress (key2 : Verity.Core.Uint256)
      let word : Verity.Core.Uint256 := value
      let flatStorage :=
        slots.foldl
          (fun current slot =>
            storeMappingEntryNat oracle current (oracle.mappingSlot slot key1) key2 value)
          (storageNatView world)
      (world.withStorageChannel
          (fun _ => fun s => ((flatStorage (wordNormalize s) : Verity.Core.Uint256)))).writeMap2
        slot key1Addr key2Addr word

def writeAddressKeyedMapping2WordSlots (oracle : DenoteOracle)
    (world : Verity.ContractState) (slots : List Nat) (key1 key2 wordOffset value : Nat) :
    Verity.ContractState :=
  let word : Verity.Core.Uint256 := value
  let targets := slots.map (fun slot =>
    wordNormalize
      (oracle.mappingSlot (oracle.mappingSlot slot key1) key2 + wordOffset))
  world.writeSlots targets word

def writeAddressKeyedMappingWordFieldSlots (oracle : DenoteOracle)
    (fields : List Field) (fieldName : String)
    (world : Verity.ContractState) (slots : List Nat) (key wordOffset value : Nat) :
    Verity.ContractState :=
  let targets := slots.map (fun slot => wordNormalize (oracle.mappingSlot slot key + wordOffset))
  writeMappingTargets fields fieldName world targets value

def writeAddressKeyedMappingFieldSlots (oracle : DenoteOracle)
    (fields : List Field) (fieldName : String)
    (world : Verity.ContractState) (slots : List Nat) (key value : Nat) :
    Verity.ContractState :=
  if fieldIsTransient fields fieldName then
    let targets := slots.map (fun slot => wordNormalize (oracle.mappingSlot slot key))
    writeTransientTargets world targets value
  else
    writeAddressKeyedMappingSlots oracle world slots key value

def writeAddressKeyedMappingChainFieldSlots (oracle : DenoteOracle)
    (fields : List Field) (fieldName : String)
    (world : Verity.ContractState) (slots keys : List Nat) (value : Nat) :
    Verity.ContractState :=
  if fieldIsTransient fields fieldName then
    let targets := slots.map (fun slot => wordNormalize (keys.foldl oracle.mappingSlot slot))
    writeTransientTargets world targets value
  else
    writeAddressKeyedMappingChainSlots oracle world slots keys value

def writeAddressKeyedMapping2WordFieldSlots (oracle : DenoteOracle)
    (fields : List Field) (fieldName : String)
    (world : Verity.ContractState) (slots : List Nat) (key1 key2 wordOffset value : Nat) :
    Verity.ContractState :=
  let targets := slots.map (fun slot =>
    wordNormalize (oracle.mappingSlot (oracle.mappingSlot slot key1) key2 + wordOffset))
  writeMappingTargets fields fieldName world targets value

def writeUintKeyedMappingFieldSlots (oracle : DenoteOracle)
    (fields : List Field) (fieldName : String)
    (world : Verity.ContractState) (slots : List Nat) (key value : Nat) :
    Verity.ContractState :=
  if fieldIsTransient fields fieldName then
    let targets := slots.map (fun slot => wordNormalize (oracle.mappingSlot slot key))
    writeTransientTargets world targets value
  else
    writeUintKeyedMappingSlots oracle world slots key value

def writeAddressKeyedMapping2FieldSlots (oracle : DenoteOracle)
    (fields : List Field) (fieldName : String)
    (world : Verity.ContractState) (slots : List Nat) (key1 key2 value : Nat) :
    Verity.ContractState :=
  if fieldIsTransient fields fieldName then
    let targets := slots.map (fun slot =>
      wordNormalize (oracle.mappingSlot (oracle.mappingSlot slot key1) key2))
    writeTransientTargets world targets value
  else
    writeAddressKeyedMapping2Slots oracle world slots key1 key2 value

def writeAddressKeyedMapping2PackedWordSlots (oracle : DenoteOracle)
    (world : Verity.ContractState) (slots : List Nat) (key1 key2 wordOffset : Nat)
    (packed : PackedBits) (value : Nat) :
    Verity.ContractState :=
  let targets := slots.map (fun slot =>
    wordNormalize
      (oracle.mappingSlot (oracle.mappingSlot slot key1) key2 + wordOffset))
  world.modifySlots targets
    (fun current => packedWordWrite current.val value packed)

def writeAddressKeyedMapping2PackedWordFieldSlots (oracle : DenoteOracle)
    (fields : List Field) (fieldName : String)
    (world : Verity.ContractState) (slots : List Nat) (key1 key2 wordOffset : Nat)
    (packed : PackedBits) (value : Nat) :
    Verity.ContractState :=
  let targets := slots.map (fun slot =>
    wordNormalize (oracle.mappingSlot (oracle.mappingSlot slot key1) key2 + wordOffset))
  if fieldIsTransient fields fieldName then
    world.modifyTransientSlots targets
      (fun current => packedWordWrite current.val value packed)
  else
    writeAddressKeyedMapping2PackedWordSlots oracle world slots key1 key2 wordOffset packed value

def storageArraySetAt :
    List Verity.Core.Uint256 → Nat → Verity.Core.Uint256 → Option (List Verity.Core.Uint256)
  | [], _, _ => none
  | _ :: rest, 0, value => some (value :: rest)
  | head :: rest, idx + 1, value => do
      let updatedRest ← storageArraySetAt rest idx value
      some (head :: updatedRest)

def storageArrayDropLast? : List Verity.Core.Uint256 → Option (List Verity.Core.Uint256)
  | [] => none
  | [_] => some []
  | head :: rest => do
      let updatedRest ← storageArrayDropLast? rest
      some (head :: updatedRest)

def writeStorageArray (world : Verity.ContractState) (slot : Nat)
    (values : List Verity.Core.Uint256) : Verity.ContractState :=
  world.writeArray slot values

/-- Ceiling-division helper matching Solidity's `Math256.ceilDiv`. -/
def ceilDivVal (lhs rhs : Verity.Core.Uint256) : Nat :=
  if lhs == 0 then 0 else ((lhs - 1) / rhs + 1).val

def dynamicArrayBinding? (bindings : Env) (name : String) :
    Option (Nat × Nat) :=
  DynamicAbi.dynamicArrayBinding? bindings name

abbrev arrayElement? := DynamicAbi.arrayElement?

abbrev externalCalldataSize :=
  DynamicAbi.externalCalldataSize

abbrev externalWordAt? :=
  DynamicAbi.externalWordAt?

abbrev arrayElementDynamicHeadOffset? :=
  DynamicAbi.arrayElementDynamicHeadOffset?

abbrev arrayElementDynamicWord? :=
  DynamicAbi.arrayElementDynamicWord?

abbrev arrayElementDynamicMemberLength? :=
  DynamicAbi.arrayElementDynamicMemberLength?

abbrev arrayElementDynamicMemberDataOffset? :=
  DynamicAbi.arrayElementDynamicMemberDataOffset?

abbrev arrayElementDynamicMemberElement? :=
  DynamicAbi.arrayElementDynamicMemberElement?

/-! ## Expression denotation (mirrors `SourceSemantics.evalExpr` arm-for-arm) -/

def evalExpr (oracle : DenoteOracle) (fields : List Field) (state : DenoteState) :
    Expr → Option Nat
  | .memoryArrayLength name =>
      lookupBinding? state.bindings s!"{name}_length"
  | .memoryArrayElement name index => do
      let idx ← evalExpr oracle fields state index
      let (dataOffset, length) ← dynamicArrayBinding? state.bindings name
      if idx < length then
        some (state.world.memory (wordNormalize (dataOffset + 32 * idx))).val
      else
        none
  | .arrayLength name =>
      lookupBinding? state.bindings s!"{name}_length"
  | .arrayElement name index => do
      let idx ← evalExpr oracle fields state index
      let (dataOffset, length) ← dynamicArrayBinding? state.bindings name
      arrayElement? state.selector state.world.calldata dataOffset length idx
  | .dynamicBytesEq lhsName rhsName => do
      let (lhsOffset, lhsLength) ← dynamicArrayBinding? state.bindings lhsName
      let (rhsOffset, rhsLength) ← dynamicArrayBinding? state.bindings rhsName
      some (boolWord (DynamicAbi.dynamicBytesEqCalldata state.selector state.world.calldata
        lhsOffset lhsLength rhsOffset rhsLength))
  | .arrayElementDynamicDataOffset name index => do
      let idx ← evalExpr oracle fields state index
      let (dataOffset, length) ← dynamicArrayBinding? state.bindings name
      arrayElementDynamicHeadOffset? state.selector state.world.calldata dataOffset length idx
  | .arrayElementDynamicMemberLength name index wordOffset => do
      let idx ← evalExpr oracle fields state index
      let (dataOffset, length) ← dynamicArrayBinding? state.bindings name
      arrayElementDynamicMemberLength?
        state.selector state.world.calldata dataOffset length idx wordOffset
  | .arrayElementDynamicMemberDataOffset name index wordOffset => do
      let idx ← evalExpr oracle fields state index
      let (dataOffset, length) ← dynamicArrayBinding? state.bindings name
      arrayElementDynamicMemberDataOffset?
        state.selector state.world.calldata dataOffset length idx wordOffset
  | .arrayElementDynamicMemberElement name index wordOffset innerIndex => do
      let idx ← evalExpr oracle fields state index
      let innerIdx ← evalExpr oracle fields state innerIndex
      let (dataOffset, length) ← dynamicArrayBinding? state.bindings name
      arrayElementDynamicMemberElement?
        state.selector state.world.calldata dataOffset length idx wordOffset innerIdx
  | .paramDynamicMemberLength _ _ => none
  | .paramDynamicMemberDataOffset _ _ => none
  | .paramDynamicMemberElement _ _ _ => none
  | .paramDynamicStaticComposite _ _ => none
  | .literal n => some (wordNormalize n)
  | .param name => some (lookupValue state.bindings name)
  | .immutable name => some (state.immutable name).val
  | .storage fieldName =>
      match findFieldWithResolvedSlot fields fieldName with
      | some (field, slot) =>
          let rawWord := (readFieldWord state.world field slot).val
          match field.packedBits with
          | none => some rawWord
          | some packed =>
              some (Verity.Core.Uint256.and
                (Verity.Core.Uint256.shr packed.offset rawWord)
                (packedMaskNat packed)).val
      | none => none
  | .storageAddr fieldName =>
      match findFieldWithResolvedSlot fields fieldName with
      | some (field, slot) =>
          if field.isTransient then
            some (state.world.readTransient (wordNormalize slot)).val
          else
            some (state.world.readAddrSlot (wordNormalize slot)).val
      | none => none
  | .storageArrayLength fieldName =>
      match findFieldWithResolvedSlot fields fieldName with
      | some ({ ty := .dynamicArray _, .. }, slot) => some (state.world.readArray slot).length
      | _ => none
  | .storageArrayElement fieldName index => do
      let idx ← evalExpr oracle fields state index
      match findFieldWithResolvedSlot fields fieldName with
      | some ({ ty := .dynamicArray _, .. }, slot) =>
          match (state.world.readArray slot)[idx]? with
          | some value => some value.val
          | none => none
      | some ({ ty := .fixedArrayUint128 size, .. }, slot) =>
          readFixedUint128ArrayElement state.world slot size idx
      | _ => none
  | .caller => some state.world.sender.val
  | .contractAddress => some state.world.thisAddress.val
  | .txOrigin => some state.world.txOrigin.val
  | .chainid => some state.world.chainId.val
  | .msgValue => some state.world.msgValue.val
  | .selfBalance => some state.world.selfBalance.val
  | .blockTimestamp => some state.world.blockTimestamp.val
  | .blockNumber => some state.world.blockNumber.val
  | .blobbasefee => some state.world.blobBaseFee.val
  | .calldatasize => some state.world.calldataSize.val
  -- Mirrors `SourceSemantics.evalExpr`: the modeled fragment performs no
  -- call-family instruction, so the EIP-211 returndata buffer stays empty.
  | .returndataSize => some 0
  | .localVar name => some (lookupValue state.bindings name)
  | .add a b => do
      let lhs : Verity.Core.Uint256 := ← evalExpr oracle fields state a
      let rhs : Verity.Core.Uint256 := ← evalExpr oracle fields state b
      pure (lhs + rhs).val
  | .sub a b => do
      let lhs : Verity.Core.Uint256 := ← evalExpr oracle fields state a
      let rhs : Verity.Core.Uint256 := ← evalExpr oracle fields state b
      pure (lhs - rhs).val
  | .mul a b => do
      let lhs : Verity.Core.Uint256 := ← evalExpr oracle fields state a
      let rhs : Verity.Core.Uint256 := ← evalExpr oracle fields state b
      pure (lhs * rhs).val
  | .div a b => do
      let lhs : Verity.Core.Uint256 := ← evalExpr oracle fields state a
      let rhs : Verity.Core.Uint256 := ← evalExpr oracle fields state b
      pure (lhs / rhs).val
  | .mod a b => do
      let lhs : Verity.Core.Uint256 := ← evalExpr oracle fields state a
      let rhs : Verity.Core.Uint256 := ← evalExpr oracle fields state b
      pure (lhs % rhs).val
  | .bitAnd a b => do
      let lhs ← evalExpr oracle fields state a
      let rhs ← evalExpr oracle fields state b
      pure (Verity.Core.Uint256.and lhs rhs).val
  | .bitOr a b => do
      let lhs ← evalExpr oracle fields state a
      let rhs ← evalExpr oracle fields state b
      pure (Verity.Core.Uint256.or lhs rhs).val
  | .bitXor a b => do
      let lhs ← evalExpr oracle fields state a
      let rhs ← evalExpr oracle fields state b
      pure (Verity.Core.Uint256.xor lhs rhs).val
  | .bitNot a => do
      let value ← evalExpr oracle fields state a
      pure (Verity.Core.Uint256.not value).val
  | .eq a b => do
      let lhs ← evalExpr oracle fields state a
      let rhs ← evalExpr oracle fields state b
      pure (boolWord (decide (lhs = rhs)))
  | .ge a b => do
      let lhs ← evalExpr oracle fields state a
      let rhs ← evalExpr oracle fields state b
      pure (boolWord (decide (rhs ≤ lhs)))
  | .gt a b => do
      let lhs ← evalExpr oracle fields state a
      let rhs ← evalExpr oracle fields state b
      pure (boolWord (decide (rhs < lhs)))
  | .lt a b => do
      let lhs ← evalExpr oracle fields state a
      let rhs ← evalExpr oracle fields state b
      pure (boolWord (decide (lhs < rhs)))
  | .le a b => do
      let lhs ← evalExpr oracle fields state a
      let rhs ← evalExpr oracle fields state b
      pure (boolWord (decide (lhs ≤ rhs)))
  | .logicalAnd a b => do
      let lhs ← evalExpr oracle fields state a
      let rhs ← evalExpr oracle fields state b
      pure (boolWord (decide (lhs != 0) && decide (rhs != 0)))
  | .logicalOr a b => do
      let lhs ← evalExpr oracle fields state a
      let rhs ← evalExpr oracle fields state b
      pure (boolWord (decide (lhs != 0) || decide (rhs != 0)))
  | .logicalNot a => do
      let value ← evalExpr oracle fields state a
      pure (boolWord (decide (value = 0)))
  | .min a b => do
      let lhs ← evalExpr oracle fields state a
      let rhs ← evalExpr oracle fields state b
      pure (if lhs ≤ rhs then lhs else rhs)
  | .max a b => do
      let lhs ← evalExpr oracle fields state a
      let rhs ← evalExpr oracle fields state b
      pure (if rhs ≤ lhs then lhs else rhs)
  | .wMulDown a b => do
      let lhs : Verity.Core.Uint256 := ← evalExpr oracle fields state a
      let rhs : Verity.Core.Uint256 := ← evalExpr oracle fields state b
      let wad : Verity.Core.Uint256 := 1000000000000000000
      pure ((lhs * rhs) / wad).val
  | .wDivUp a b => do
      let lhs : Verity.Core.Uint256 := ← evalExpr oracle fields state a
      let rhs : Verity.Core.Uint256 := ← evalExpr oracle fields state b
      let wad : Verity.Core.Uint256 := 1000000000000000000
      pure (((lhs * wad) + (rhs - 1)) / rhs).val
  | .ceilDiv a b => do
      let lhs : Verity.Core.Uint256 := ← evalExpr oracle fields state a
      let rhs : Verity.Core.Uint256 := ← evalExpr oracle fields state b
      pure (ceilDivVal lhs rhs)
  | .mulDivDown a b c => do
      let lhs : Verity.Core.Uint256 := ← evalExpr oracle fields state a
      let rhs : Verity.Core.Uint256 := ← evalExpr oracle fields state b
      let denom : Verity.Core.Uint256 := ← evalExpr oracle fields state c
      pure ((lhs * rhs) / denom).val
  | .mulDivUp a b c => do
      let lhs : Verity.Core.Uint256 := ← evalExpr oracle fields state a
      let rhs : Verity.Core.Uint256 := ← evalExpr oracle fields state b
      let denom : Verity.Core.Uint256 := ← evalExpr oracle fields state c
      pure (((lhs * rhs) + (denom - 1)) / denom).val
  | .ite cond thenVal elseVal => do
      let condVal ← evalExpr oracle fields state cond
      if condVal != 0 then
        evalExpr oracle fields state thenVal
      else
        evalExpr oracle fields state elseVal
  | .forkIfAtLeast _ _ _ => none
  | .shl shift value => do
      let shiftVal ← evalExpr oracle fields state shift
      let wordVal ← evalExpr oracle fields state value
      pure (Verity.Core.Uint256.shl shiftVal wordVal).val
  | .shr shift value => do
      let shiftVal ← evalExpr oracle fields state shift
      let wordVal ← evalExpr oracle fields state value
      pure (Verity.Core.Uint256.shr shiftVal wordVal).val
  | .slt a b => do
      let lhs ← evalExpr oracle fields state a
      let rhs ← evalExpr oracle fields state b
      pure (boolWord (decide (
        (Verity.Core.Int256.ofUint256 (Verity.Core.Uint256.ofNat lhs) : Int) <
        (Verity.Core.Int256.ofUint256 (Verity.Core.Uint256.ofNat rhs) : Int))))
  | .sgt a b => do
      let lhs ← evalExpr oracle fields state a
      let rhs ← evalExpr oracle fields state b
      pure (boolWord (decide (
        (Verity.Core.Int256.ofUint256 (Verity.Core.Uint256.ofNat rhs) : Int) <
        (Verity.Core.Int256.ofUint256 (Verity.Core.Uint256.ofNat lhs) : Int))))
  | .sdiv a b => do
      let lhs ← evalExpr oracle fields state a
      let rhs ← evalExpr oracle fields state b
      pure (Verity.Core.Int256.div
        (Verity.Core.Int256.ofUint256 (Verity.Core.Uint256.ofNat lhs))
        (Verity.Core.Int256.ofUint256 (Verity.Core.Uint256.ofNat rhs))).toUint256.val
  | .smod a b => do
      let lhs ← evalExpr oracle fields state a
      let rhs ← evalExpr oracle fields state b
      pure (Verity.Core.Int256.mod
        (Verity.Core.Int256.ofUint256 (Verity.Core.Uint256.ofNat lhs))
        (Verity.Core.Int256.ofUint256 (Verity.Core.Uint256.ofNat rhs))).toUint256.val
  | .sar a b => do
      let lhs ← evalExpr oracle fields state a
      let rhs ← evalExpr oracle fields state b
      pure (Verity.Core.Int256.sar
        (Verity.Core.Int256.ofUint256 (Verity.Core.Uint256.ofNat lhs))
        (Verity.Core.Int256.ofUint256 (Verity.Core.Uint256.ofNat rhs))).toUint256.val
  | .byte a b => do
      let index ← evalExpr oracle fields state a
      let value ← evalExpr oracle fields state b
      pure (Verity.Core.Uint256.byte
        (Verity.Core.Uint256.ofNat index)
        (Verity.Core.Uint256.ofNat value)).val
  | .signextend a b => do
      let byteIdx ← evalExpr oracle fields state a
      let value ← evalExpr oracle fields state b
      pure (Verity.Core.Uint256.signextend
        (Verity.Core.Uint256.ofNat byteIdx)
        (Verity.Core.Uint256.ofNat value)).val
  | .mapping field key => do
      let keyVal ← evalExpr oracle fields state key
      match findFieldWithResolvedSlot fields field with
      | some (field, slot) =>
          some (readFieldWord state.world field (oracle.mappingSlot slot keyVal)).val
      | none => none
  | .mappingWord field key wordOffset => do
      let keyVal ← evalExpr oracle fields state key
      match findFieldWithResolvedSlot fields field with
      | some (field, slot) =>
          some (readFieldWord state.world field
            (wordNormalize (oracle.mappingSlot slot keyVal + wordOffset))).val
      | none => none
  | .mappingUint field key => do
      let keyVal ← evalExpr oracle fields state key
      match findFieldWithResolvedSlot fields field with
      | some (field, slot) =>
          some (readFieldWord state.world field (oracle.mappingSlot slot keyVal)).val
      | none => none
  | .mapping2 field key1 key2 => do
      let key1Val ← evalExpr oracle fields state key1
      let key2Val ← evalExpr oracle fields state key2
      match findFieldWithResolvedSlot fields field with
      | some (field, slot) =>
          let innerSlot := oracle.mappingSlot slot key1Val
          some (readFieldWord state.world field (oracle.mappingSlot innerSlot key2Val)).val
      | none => none
  | .mapping2Word field key1 key2 wordOffset => do
      let key1Val ← evalExpr oracle fields state key1
      let key2Val ← evalExpr oracle fields state key2
      match findFieldWithResolvedSlot fields field with
      | some (field, slot) =>
          let innerSlot := oracle.mappingSlot slot key1Val
          let outerSlot := oracle.mappingSlot innerSlot key2Val
          some (readFieldWord state.world field (wordNormalize (outerSlot + wordOffset))).val
      | none => none
  | .mappingChain field [key] => do
      let keyVal ← evalExpr oracle fields state key
      match findFieldWithResolvedSlot fields field with
      | some (field, slot) =>
          some (readFieldWord state.world field (oracle.mappingSlot slot keyVal)).val
      | none => none
  | .mappingChain field [key1, key2] => do
      let key1Val ← evalExpr oracle fields state key1
      let key2Val ← evalExpr oracle fields state key2
      match findFieldWithResolvedSlot fields field with
      | some (field, slot) =>
          let innerSlot := oracle.mappingSlot slot key1Val
          some (readFieldWord state.world field (oracle.mappingSlot innerSlot key2Val)).val
      | none => none
  -- Longer mappingChain reads: deferred, exactly as in SourceSemantics.
  | .structMember field key memberName => do
      let keyVal ← evalExpr oracle fields state key
      match findFieldWithResolvedSlot fields field, findStructMembers fields field with
      | some (fieldInfo, slot), some members =>
          match findStructMember members memberName with
          | some member =>
              let targetSlot := wordNormalize
                (oracle.mappingSlot slot keyVal + member.wordOffset)
              let rawWord := (readFieldWord state.world fieldInfo targetSlot).val
              match member.packed with
              | none => some rawWord
              | some packed =>
                  some (Verity.Core.Uint256.and
                    (Verity.Core.Uint256.shr packed.offset rawWord)
                    (packedMaskNat packed)).val
          | none => none
      | _, _ => none
  | .structMember2 field key1 key2 memberName => do
      let key1Val ← evalExpr oracle fields state key1
      let key2Val ← evalExpr oracle fields state key2
      match findFieldWithResolvedSlot fields field, findStructMembers fields field with
      | some (fieldInfo, slot), some members =>
          match findStructMember members memberName with
          | some member =>
              let innerSlot := oracle.mappingSlot slot key1Val
              let outerSlot := oracle.mappingSlot innerSlot key2Val
              let targetSlot := wordNormalize (outerSlot + member.wordOffset)
              let rawWord := (readFieldWord state.world fieldInfo targetSlot).val
              match member.packed with
              | none => some rawWord
              | some packed =>
                  some (Verity.Core.Uint256.and
                    (Verity.Core.Uint256.shr packed.offset rawWord)
                    (packedMaskNat packed)).val
          | none => none
      | _, _ => none
  | .mappingPackedWord field key wordOffset packed => do
      let keyVal ← evalExpr oracle fields state key
      match findFieldWithResolvedSlot fields field with
      | some (fieldInfo, slot) =>
          let targetSlot := wordNormalize
            (oracle.mappingSlot slot keyVal + wordOffset)
          let rawWord := (readFieldWord state.world fieldInfo targetSlot).val
          some (Verity.Core.Uint256.and
            (Verity.Core.Uint256.shr packed.offset rawWord)
            (packedMaskNat packed)).val
      | none => none
  | .mload offset => do
      let resolvedOffset ← evalExpr oracle fields state offset
      some (state.world.memory resolvedOffset).val
  | .tload offset => do
      let resolvedOffset ← evalExpr oracle fields state offset
      some (state.world.readTransient resolvedOffset).val
  | .calldataload offset => do
      let resolvedOffset ← evalExpr oracle fields state offset
      some (calldataloadWord state.selector state.world.calldata resolvedOffset)
  | .extcodesize addr => do
      let resolvedAddr ← evalExpr oracle fields state addr
      some (state.world.codeSize (resolvedAddr % Compiler.Constants.addressModulus)).val
  | .returndataOptionalBoolAt offset => do
      let _ ← evalExpr oracle fields state offset
      some 1
  -- The reserved `exp` builtin lane: pure arithmetic wearing an `externalCall`
  -- node, so it needs no oracle. Genuine foreign calls stay undenoted.
  | .externalCall name [base, exponent] =>
      if name == builtinExpName then do
        let baseVal ← evalExpr oracle fields state base
        let exponentVal ← evalExpr oracle fields state exponent
        pure (Verity.Core.Uint256.powEff
          (Verity.Core.Uint256.ofNat baseVal)
          (Verity.Core.Uint256.ofNat exponentVal)).val
      else none
  | .keccak256 offExpr sizeExpr => do
      let off ← evalExpr oracle fields state offExpr
      let size ← evalExpr oracle fields state sizeExpr
      some (oracle.keccakMemorySlice state.world.memory off size)
  | .constructorArg idx =>
      lookupBinding? state.bindings s!"arg{idx}"
  | .arrayElementDynamicWord name index wordOffset => do
      let idx ← evalExpr oracle fields state index
      let (dataOffset, length) ← dynamicArrayBinding? state.bindings name
      arrayElementDynamicWord?
        state.selector state.world.calldata dataOffset length idx wordOffset
  | _ => none

def evalExprList (oracle : DenoteOracle) (fields : List Field) (state : DenoteState) :
    List Expr → Option (List Nat)
  | [] => some []
  | expr :: rest => do
      let value ← evalExpr oracle fields state expr
      let values ← evalExprList oracle fields state rest
      pure (value :: values)

/-! ## Statement denotation (mirrors event-less `SourceSemantics.execStmt`) -/

def valuesAsEventArgs (values : List Nat) : List Verity.Core.Uint256 :=
  values.map (fun value => Verity.Core.Uint256.ofNat value)

def execForEachLoop
    (varName : String)
    (runBody : DenoteState → StmtOutcome) :
    DenoteState → Nat → Nat → StmtOutcome
  | state, _, 0 => .continue state
  | state, index, remaining + 1 =>
      let loopState :=
        { state with bindings := bindValue state.bindings varName (wordNormalize index) }
      match runBody loopState with
      | .continue next => execForEachLoop varName runBody next (index + 1) remaining
      | .stop next => .stop next
      | .return value next => .return value next
      | .revert => .revert

def msbIndex (bitmap : Nat) : Nat :=
  if bitmap = 0 then 0 else Nat.log2 bitmap

def clearMsb (bitmap : Nat) : Nat :=
  let idx := msbIndex bitmap
  if bitmap = 0 then 0 else bitmap - 2 ^ idx

def execForEachSetBitLoop
    (varName : String)
    (runBody : DenoteState → StmtOutcome) :
    Nat → DenoteState → Nat → StmtOutcome
  | 0, state, _ => .continue state
  | fuel + 1, state, bitmap =>
      if bitmap = 0 then
        .continue state
      else
        let idx := msbIndex bitmap
        let loopState :=
          { state with bindings := bindValue state.bindings varName (wordNormalize idx) }
        match runBody loopState with
        | .continue next => execForEachSetBitLoop varName runBody fuel next (clearMsb bitmap)
        | .stop next => .stop next
        | .return value next => .return value next
        | .revert => .revert

mutual
  def execStmt (oracle : DenoteOracle) (fields : List Field) :
      DenoteState → Stmt → StmtOutcome
    | state, .letVar name value =>
        match evalExpr oracle fields state value with
        | some resolved =>
            .continue { state with bindings := bindValue state.bindings name resolved }
        | none => .revert
    | state, .assignVar name value =>
        match evalExpr oracle fields state value with
        | some resolved =>
            .continue { state with bindings := bindValue state.bindings name resolved }
        | none => .revert
    | state, .setStorage fieldName value =>
        match findFieldWriteSlots fields fieldName, evalExpr oracle fields state value with
        | some slots, some resolved =>
            .continue { state with world := writeUintFieldSlots fields fieldName state.world slots resolved }
        | _, _ => .revert
    | state, .setStorageWord fieldName wordOffset value =>
        match findFieldWriteSlots fields fieldName, evalExpr oracle fields state value with
        | some slots, some resolved =>
            .continue
              { state with
                  world := writeStorageWordFieldSlots fields fieldName state.world slots wordOffset resolved }
        | _, _ => .revert
    | state, .setMapping fieldName key value =>
        match findFieldWriteSlots fields fieldName,
            evalExpr oracle fields state key,
            evalExpr oracle fields state value with
        | some slots@(_ :: _), some resolvedKey, some resolved =>
            .continue
              { state with
                  world := writeAddressKeyedMappingFieldSlots
                    oracle fields fieldName state.world slots resolvedKey resolved }
        | _, _, _ => .revert
    | state, .setMappingWord fieldName key wordOffset value =>
        match findFieldWriteSlots fields fieldName,
            evalExpr oracle fields state key,
            evalExpr oracle fields state value with
        | some slots@(_ :: _), some resolvedKey, some resolved =>
            .continue
               { state with
                   world := writeAddressKeyedMappingWordFieldSlots
                     oracle fields fieldName state.world slots resolvedKey wordOffset resolved }
        | _, _, _ => .revert
    | state, .setMappingPackedWord fieldName key wordOffset packed value =>
        match findFieldWriteSlots fields fieldName,
            evalExpr oracle fields state key,
            evalExpr oracle fields state value with
        | some slots@(_ :: _), some resolvedKey, some resolved =>
            if packedBitsValid packed then
              .continue
                { state with
                    world := writeAddressKeyedMappingPackedWordFieldSlots oracle
                      fields fieldName state.world slots resolvedKey wordOffset packed resolved }
            else
              .revert
        | _, _, _ => .revert
    | state, .setStructMember fieldName key memberName value =>
        match findFieldWriteSlots fields fieldName,
            findStructMembers fields fieldName,
            evalExpr oracle fields state key,
            evalExpr oracle fields state value with
        | some slots@(_ :: _), some members, some resolvedKey, some resolved =>
            match findStructMember members memberName with
            | some { wordOffset := wordOffset, packed := none, .. } =>
                .continue
                  { state with
                      world := writeAddressKeyedMappingWordFieldSlots
                        oracle fields fieldName state.world slots resolvedKey wordOffset resolved }
            | some { wordOffset := wordOffset, packed := some packed, .. } =>
                if packedBitsValid packed then
                  .continue
                    { state with
                        world := writeAddressKeyedMappingPackedWordFieldSlots oracle
                          fields fieldName state.world slots resolvedKey wordOffset packed resolved }
                else
                  .revert
            | _ => .revert
        | _, _, _, _ => .revert
    | state, .setMapping2 fieldName key1 key2 value =>
        match findFieldWriteSlots fields fieldName,
            evalExpr oracle fields state key1,
            evalExpr oracle fields state key2,
            evalExpr oracle fields state value with
        | some slots@(_ :: _), some resolvedKey1, some resolvedKey2, some resolved =>
            .continue
              { state with
                  world :=
                    writeAddressKeyedMapping2FieldSlots
                      oracle fields fieldName state.world slots resolvedKey1 resolvedKey2 resolved }
        | _, _, _, _ => .revert
    | state, .setMapping2Word fieldName key1 key2 wordOffset value =>
        match findFieldWriteSlots fields fieldName,
            evalExpr oracle fields state key1,
            evalExpr oracle fields state key2,
            evalExpr oracle fields state value with
        | some slots@(_ :: _), some resolvedKey1, some resolvedKey2, some resolved =>
            .continue
              { state with
                  world :=
                    writeAddressKeyedMapping2WordFieldSlots oracle
                      fields
                      fieldName
                      state.world
                      slots
                      resolvedKey1
                      resolvedKey2
                      wordOffset
                      resolved }
        | _, _, _, _ => .revert
    | state, .setStructMember2 fieldName key1 key2 memberName value =>
        match findFieldWriteSlots fields fieldName,
            findStructMembers fields fieldName,
            evalExpr oracle fields state key1,
            evalExpr oracle fields state key2,
            evalExpr oracle fields state value with
        | some slots@(_ :: _), some members, some resolvedKey1, some resolvedKey2, some resolved =>
            match findStructMember members memberName with
            | some { wordOffset := wordOffset, packed := none, .. } =>
                .continue
                  { state with
                      world := writeAddressKeyedMapping2WordFieldSlots
                        oracle fields fieldName state.world slots resolvedKey1 resolvedKey2 wordOffset resolved }
            | some { wordOffset := wordOffset, packed := some packed, .. } =>
                if packedBitsValid packed then
                  .continue
                    { state with
                        world := writeAddressKeyedMapping2PackedWordFieldSlots oracle
                          fields fieldName state.world slots resolvedKey1 resolvedKey2 wordOffset packed resolved }
                else
                  .revert
            | _ => .revert
        | _, _, _, _, _ => .revert
    | state, .setMappingUint fieldName key value =>
        match findFieldWriteSlots fields fieldName,
            evalExpr oracle fields state key,
            evalExpr oracle fields state value with
        | some slots@(_ :: _), some resolvedKey, some resolved =>
            .continue
              { state with
                  world := writeUintKeyedMappingFieldSlots
                    oracle fields fieldName state.world slots resolvedKey resolved }
        | _, _, _ => .revert
    | state, .setMappingChain fieldName keys value =>
        match findFieldWriteSlots fields fieldName,
            evalExprList oracle fields state keys,
            evalExpr oracle fields state value with
        | some slots@(_ :: _), some resolvedKeys, some resolved =>
            .continue
              { state with
                  world := writeAddressKeyedMappingChainFieldSlots
                    oracle fields fieldName state.world slots resolvedKeys resolved }
        | _, _, _ => .revert
    | state, .storageArrayPush fieldName value =>
        match findFieldWithResolvedSlot fields fieldName, evalExpr oracle fields state value with
        | some ({ ty := .dynamicArray _, .. }, slot), some resolved =>
            let updated := state.world.readArray slot ++ [(resolved : Verity.Core.Uint256)]
            .continue { state with world := writeStorageArray state.world slot updated }
        | _, _ => .revert
    | state, .storageArrayPop fieldName =>
        match findFieldWithResolvedSlot fields fieldName with
        | some ({ ty := .dynamicArray _, .. }, slot) =>
            match storageArrayDropLast? (state.world.readArray slot) with
            | some updated =>
                .continue { state with world := writeStorageArray state.world slot updated }
            | none => .revert
        | _ => .revert
    | state, .setStorageArrayElement fieldName index value =>
        match findFieldWithResolvedSlot fields fieldName,
            evalExpr oracle fields state index,
            evalExpr oracle fields state value with
        | some ({ ty := .dynamicArray _, .. }, slot), some idx, some resolved =>
            match storageArraySetAt (state.world.readArray slot) idx resolved with
            | some updated =>
                .continue { state with world := writeStorageArray state.world slot updated }
            | none => .revert
        | some ({ ty := .fixedArrayUint128 size, .. }, _), some idx, some resolved =>
            match findFieldWriteSlots fields fieldName >>= fun slots =>
                writeFixedUint128ArrayElementSlots state.world slots size idx resolved with
            | some world => .continue { state with world := world }
            | none => .revert
        | _, _, _ => .revert
    | state, .setStorageAddr fieldName value =>
        match findFieldWriteSlots fields fieldName, evalExpr oracle fields state value with
        | some slots, some resolved =>
            .continue { state with world := writeAddressFieldSlots fields fieldName state.world slots resolved }
        | _, _ => .revert
    | state, .setImmutable name value =>
        match evalExpr oracle fields state value with
        | some resolved =>
            .continue
              { state with
                  immutable := fun immName =>
                    if immName == name then resolved else state.immutable immName }
        | none => .revert
    | state, .mstore offset value =>
        match evalExpr oracle fields state offset, evalExpr oracle fields state value with
        | some resolvedOffset, some resolvedValue =>
            .continue {
              state with
              world := {
                state.world with
                memory := fun o =>
                  if o = resolvedOffset then resolvedValue else state.world.memory o
              }
            }
        | _, _ => .revert
    | state, .tstore offset value =>
        match evalExpr oracle fields state offset, evalExpr oracle fields state value with
        | some resolvedOffset, some resolvedValue =>
            let resolvedOffset := wordNormalize resolvedOffset
            .continue {
              state with
              world := state.world.writeTransient resolvedOffset resolvedValue
            }
        | _, _ => .revert
    | state, .calldatacopy destOffset sourceOffset size =>
        match evalExpr oracle fields state destOffset, evalExpr oracle fields state sourceOffset,
            evalExpr oracle fields state size with
        | some dst, some src, some sz =>
            .continue {
              state with
              world := {
                state.world with
                memory := fun o =>
                  if calldatacopyWritesAt dst sz o then
                    Verity.Core.Uint256.ofNat
                      (calldataloadWord state.selector state.world.calldata (src + (o - dst)))
                  else state.world.memory o
              }
            }
        | _, _, _ => .revert
    | state, .returndataCopy destOffset sourceOffset size =>
        match evalExpr oracle fields state destOffset, evalExpr oracle fields state sourceOffset,
            evalExpr oracle fields state size with
        | some _, some src, some sz =>
            if src + sz = 0 then .continue state else .revert
        | _, _, _ => .revert
    | state, .require cond _ =>
        match evalExpr oracle fields state cond with
        | some resolved =>
            if resolved != 0 then .continue state else .revert
        | none => .revert
    | state, .requireError cond _ args =>
        match evalExpr oracle fields state cond with
        | some resolved =>
            if resolved != 0 then
              .continue state
            else
              match evalExprList oracle fields state args with
              | _ => .revert
        | none => .revert
    | state, .revertError _ args =>
        match evalExprList oracle fields state args with
        | _ => .revert
    | state, .panicCode code =>
        match evalExpr oracle fields state code with
        | some _ => .revert
        | none => .revert
    | state, .return value =>
        match evalExpr oracle fields state value with
        | some resolved => .return resolved
            { state with
                world := { state.world with
                  memory := fun o => if o = 0 then resolved else state.world.memory o } }
        | none => .revert
    | state, .stop => .stop state
    | state, .ite cond thenBranch elseBranch =>
        match evalExpr oracle fields state cond with
        | some resolved =>
            if resolved != 0 then
              execStmtList oracle fields state thenBranch
            else
              execStmtList oracle fields state elseBranch
        | none => .revert
    | state, .emit eventName args =>
        match evalExprList oracle fields state args with
        | some resolved =>
            -- Event-less semantics: matches `SourceSemantics.execStmt`'s `.emit`
            -- arm, which calls the event helpers with an empty `EventDef` list.
            .continue { state with
              world := {
                state.world with
                events := state.world.events ++
                  [{ name := eventName
                     args := valuesAsEventArgs resolved
                     indexedArgs := [] }] } }
        | none => .revert
    | state, .forEach varName count body =>
        match evalExpr oracle fields state count with
        | some bound =>
            let initialLoopState :=
              { state with bindings := bindValue state.bindings varName (wordNormalize 0) }
            execForEachLoop varName
              (fun loopState => execStmtList oracle fields loopState body)
              initialLoopState 0 bound
        | none => .revert
    | state, .forEachSetBit varName bitmap body =>
        match evalExpr oracle fields state bitmap with
        | some bits =>
            execForEachSetBitLoop varName
              (fun loopState => execStmtList oracle fields loopState body)
              256 state bits
        | none => .revert
    | state, .externalCallBind resultVars _externalName args =>
        match evalExprList oracle fields state args with
        | some _ =>
            if state.externalCallSucceeded state.externalCallIndex then
              let retVals := state.externalCallReturnValues state.externalCallIndex
              if retVals.length < resultVars.length then .revert
              else
                .continue
                  { state with
                      world := (state.externalCallPostWorld state.externalCallIndex).getD
                        state.world
                      bindings := bindValues state.bindings resultVars
                        (retVals.map wordNormalize)
                      externalCallIndex := state.externalCallIndex + 1 }
            else .revert
        | none => .revert
    | state, .tryExternalCallBind successVar resultVars _externalName args =>
        match evalExprList oracle fields state args with
        | some _ =>
            let retVals := state.externalCallReturnValues state.externalCallIndex
            if state.externalCallSucceeded state.externalCallIndex then
              if retVals.length < resultVars.length then .revert
              else
                .continue
                  { state with
                      world := (state.externalCallPostWorld state.externalCallIndex).getD
                        state.world
                      bindings := bindValues
                        (bindValue state.bindings successVar 1)
                        resultVars (retVals.map wordNormalize)
                      externalCallIndex := state.externalCallIndex + 1 }
            else
              .continue
                { state with
                    bindings := bindValues
                      (bindValue state.bindings successVar 0)
                      resultVars (retVals.map wordNormalize)
                    externalCallIndex := state.externalCallIndex + 1 }
        | none => .revert
    | _, .revertReturndata => .revert
    | _, _ => .revert

  def execStmtList (oracle : DenoteOracle) (fields : List Field) :
      DenoteState → List Stmt → StmtOutcome
    | state, [] => .continue state
    | state, stmt :: rest =>
        match execStmt oracle fields state stmt with
        | .continue next => execStmtList oracle fields next rest
        | .stop next => .stop next
        | .return value next => .return value next
        | .revert => .revert
end

/-! ## Function denotation (mirrors `SourceSemantics.interpretFunction`) -/

/-- Mirrors `Compiler.Proofs.IRGeneration.IRTransaction`, compiler-free. -/
structure DenoteTransaction where
  sender : Nat
  msgValue : Nat := 0
  thisAddress : Nat := 0
  blockTimestamp : Nat := 0
  blockNumber : Nat := 0
  chainId : Nat := 0
  blobBaseFee : Nat := 0
  txOrigin : Nat := 0
  functionSelector : Nat
  args : List Nat
  deriving Repr

/-- Mirrors `SourceSemantics.SourceContractResult`. -/
structure DenoteResult where
  success : Bool
  returnValue : Option Nat
  finalStorage : Nat → Nat
  events : List (List Nat)

def encodeEvent (ev : Verity.Event) : List Nat :=
  ev.indexedArgs.map (fun arg => arg.val) ++ ev.args.map (fun arg => arg.val)

def encodeEvents (events : List Verity.Event) : List (List Nat) :=
  events.map encodeEvent

def revertedResult (oracle : DenoteOracle) (spec : CompilationModel)
    (initialWorld : Verity.ContractState) : DenoteResult :=
  { success := false
    returnValue := none
    finalStorage := encodeStorage oracle spec initialWorld
    events := encodeEvents initialWorld.events }

def successResult (oracle : DenoteOracle) (spec : CompilationModel)
    (world : Verity.ContractState) (ret : Option Nat) : DenoteResult :=
  { success := true
    returnValue := ret
    finalStorage := encodeStorage oracle spec world
    events := encodeEvents world.events }

def decodeSupportedParamWord (ty : ParamType) (word : Nat) : Option Nat :=
  let word := wordNormalize word
  match ty with
  | .uint256 | .int256 | .bytes32 => some word
  | .uint8 => some (word &&& (uint8Modulus - 1))
  | .uint16 => some (word &&& (2^16 - 1))
  | .uintN bits => some (word &&& (2 ^ bits - 1))
  | .intN bits => some
      (Verity.Core.Uint256.signextend
        (Verity.Core.Uint256.ofNat (bits / 8 - 1))
        (Verity.Core.Uint256.ofNat word)).val
  | .bytesN bytes => some
      (word &&& ((2 ^ (8 * bytes) - 1) * 2 ^ (8 * (32 - bytes))))
  | .address => some (word &&& Compiler.Constants.addressMask)
  | .bool => some (if word = 0 then 0 else 1)
  | _ => none

def bindSupportedParams (params : List Param) (args : List Nat) : Option Env :=
  match params, args with
  | [], _ => some []
  | _ :: _, [] => none
  | param :: rest, arg :: restArgs => do
      let value ← decodeSupportedParamWord param.ty arg
      let bindings ← bindSupportedParams rest restArgs
      pure ((param.name, value) :: bindings)

def bindExternalParam (selector : Nat) (calldata : List Nat)
    (headSize baseOffset headOffset : Nat) (param : Param) :
    Option Env :=
  DynamicAbi.bindExternalParam selector calldata headSize baseOffset headOffset param

def bindExternalParamsFrom (selector : Nat) (calldata : List Nat)
    (headSize baseOffset : Nat) (params : List Param) (headOffset : Nat) : Option Env :=
  DynamicAbi.bindExternalParamsFrom selector calldata headSize baseOffset params headOffset

def bindExternalParams (selector : Nat) (params : List Param) (calldata : List Nat) :
    Option Env :=
  DynamicAbi.bindExternalParams selector params calldata

def withTransactionContext (world : Verity.ContractState) (tx : DenoteTransaction) :
    Verity.ContractState :=
  { world with
    sender := Verity.wordToAddress tx.sender
    thisAddress := Verity.wordToAddress tx.thisAddress
    msgValue := tx.msgValue
    blockTimestamp := tx.blockTimestamp
    blockNumber := tx.blockNumber
    chainId := tx.chainId
    blobBaseFee := tx.blobBaseFee
    txOrigin := Verity.wordToAddress tx.txOrigin
    calldataSize := Verity.Core.Uint256.ofNat (4 + tx.args.length * 32)
    calldata := tx.args }

/-- Canonical denotation of an external function of the deep model.
Mirrors `SourceSemantics.interpretFunction` with the event-less statement
semantics (see header note 2). -/
def denoteFunction (oracle : DenoteOracle) (spec : CompilationModel) (fn : FunctionSpec)
    (tx : DenoteTransaction) (initialWorld : Verity.ContractState) : DenoteResult :=
  let worldWithTx := withTransactionContext initialWorld tx
  let fields := effectiveFields spec
  match bindExternalParams tx.functionSelector fn.params tx.args with
  | none => revertedResult oracle spec worldWithTx
  | some bindings =>
      match execStmtList oracle fields
          { world := worldWithTx, bindings := bindings, selector := tx.functionSelector }
          fn.body with
      | .continue state => successResult oracle spec state.world none
      | .stop state => successResult oracle spec state.world none
      | .return value state => successResult oracle spec state.world (some value)
      | .revert => revertedResult oracle spec worldWithTx

/-! ## Smoke checks (oracle-independent scenarios) -/

private def dummyOracle : DenoteOracle :=
  { mappingSlot := fun _ _ => 0
    keccakMemorySlice := fun _ _ _ => 0 }

private def smokeSpec (body : List Stmt) : CompilationModel :=
  { name := "DenoteSmoke"
    fields := []
    constructor := none
    functions := [{ name := "f", params := [], returnType := none, body := body }] }

private def smokeFn (body : List Stmt) : FunctionSpec :=
  { name := "f", params := [], returnType := none, body := body }

private def smokeTx : DenoteTransaction :=
  { sender := 1, functionSelector := 0, args := [] }

example :
    (denoteFunction dummyOracle (smokeSpec [.return (.literal 42)])
      (smokeFn [.return (.literal 42)]) smokeTx Verity.defaultState).returnValue =
      some 42 := by native_decide

example :
    (denoteFunction dummyOracle
      (smokeSpec [.letVar "x" (.literal 7), .return (.add (.localVar "x") (.literal 5))])
      (smokeFn [.letVar "x" (.literal 7), .return (.add (.localVar "x") (.literal 5))])
      smokeTx Verity.defaultState).returnValue = some 12 := by native_decide

example :
    (denoteFunction dummyOracle (smokeSpec [.require (.literal 0) "always fails"])
      (smokeFn [.require (.literal 0) "always fails"]) smokeTx
      Verity.defaultState).success = false := by native_decide

example :
    let world := { Verity.defaultState with
      memory := fun offset => if offset = 96 then 41 else 0 }
    let state : DenoteState :=
      { world := world
        bindings := [("xs_data_offset", 96), ("xs_length", 2)] }
    evalExpr dummyOracle [] state (.memoryArrayLength "xs") = some 2 ∧
      evalExpr dummyOracle [] state (.memoryArrayElement "xs" (.literal 0)) = some 41 ∧
      evalExpr dummyOracle [] state (.memoryArrayElement "xs" (.literal 2)) = none := by
  native_decide

example :
    let body :=
      [ Stmt.letVar "xs_data_offset" (.literal 96)
      , Stmt.letVar "xs_length" (.literal 1)
      , Stmt.mstore (.literal 96) (.literal 77)
      , Stmt.return (.memoryArrayElement "xs" (.literal 0)) ]
    (denoteFunction dummyOracle (smokeSpec body) (smokeFn body)
      smokeTx Verity.defaultState).returnValue = some 77 := by
  native_decide

end Compiler.CompilationModel.Denote
