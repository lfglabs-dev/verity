import Compiler.Proofs.IRGeneration.SupportedSpec
import Compiler.Proofs.IRGeneration.IRInterpreter
import Compiler.Proofs.MappingSlot
import Compiler.CompilationModel.LayoutValidation
import Compiler.Keccak.Sponge
import Verity.Core.Model.Denote
import Verity.Core.Model.DynamicAbi

set_option linter.unnecessarySimpa false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unusedVariables false

namespace Compiler.Proofs.IRGeneration

open Compiler
open Compiler.CompilationModel

namespace SourceSemantics

def wordNormalize (n : Nat) : Nat :=
  ((n : Verity.Core.Uint256) : Nat)

@[simp] theorem wordNormalize_eq_mod (n : Nat) :
    wordNormalize n = n % Compiler.Constants.evmModulus := by
  rfl

def uint8Modulus : Nat := 2 ^ 8

def addressModulus : Nat := 2 ^ 160

def boolWord (b : Bool) : Nat :=
  if b then 1 else 0

/-- Big-endian 32-byte encoding of a 256-bit word (byte 0 most significant). -/
def wordToBytesBE (w : Nat) : ByteArray :=
  ⟨((List.range 32).map (fun i => UInt8.ofNat ((w / (256 ^ (31 - i))) % 256))).toArray⟩

/-- Concatenate the big-endian bytes of the word-aligned memory cells covering
`[offset, offset + size)` and keep the first `size` bytes.

This is faithful to EVM `keccak256(offset, size)` for the word-aligned access
pattern Verity's compiler emits: one 32-byte cell per slot at `offset + 32*i`,
matching how `mload`/`mstore` are modelled here (memory is keyed by byte offset
and returns the full word stored at that key). -/
def memorySliceBytesBE (memory : Nat → Verity.Core.Uint256) (offset size : Nat) :
    ByteArray :=
  let nWords := (size + 31) / 32
  let full := (List.range nWords).foldl
    (fun acc i => acc ++ wordToBytesBE (memory (offset + 32 * i)).val) ByteArray.empty
  full.extract 0 size

/-- Source-semantics model of `keccak256(offset, size)`: the in-tree pure Keccak
engine applied to the word-aligned memory slice, returned as a big-endian word.
Uses the real `KeccakEngine.keccak256`, so the modelled digest is the genuine
Keccak-256 of the slice (no abstract placeholder). -/
def keccakMemorySlice (memory : Nat → Verity.Core.Uint256) (offset size : Nat) : Nat :=
  abstractKeccakMemorySlice (fun address => (memory address).val) offset size

/-- Low-level proof encoding of an emitted event.

Source execution stores the same log payload shape as proof IR `log*`
execution: topics first, followed by word-aligned data words. For known events
`eventFromResolvedArgs?` places the event signature topic at the front of
`indexedArgs`, so this encoder intentionally ignores the high-level name. -/
def encodeEvent (ev : Verity.Event) : List Nat :=
  ev.indexedArgs.map (fun arg => arg.val) ++ ev.args.map (fun arg => arg.val)

def encodeEvents (events : List Verity.Event) : List (List Nat) :=
  events.map encodeEvent

def valuesAsEventArgs (values : List Nat) : List Verity.Core.Uint256 :=
  values.map (fun value => (value : Verity.Core.Uint256))

def eventSignatureMemory (eventDef : EventDef) : Nat → Nat :=
  let words :=
    (chunkBytes32 (bytesFromString (eventSignature eventDef))).map wordFromBytes
  fun offset =>
    if offset % 32 = 0 then
      (words[offset / 32]?).getD 0
    else
      0

def eventSignatureTopic (eventDef : EventDef) : Nat :=
  abstractKeccakMemorySlice (eventSignatureMemory eventDef) 0
    (bytesFromString (eventSignature eventDef)).length

def normalizeEventValue (ty : ParamType) (value : Nat) : Nat :=
  let word := wordNormalize value
  match ty with
  | .uint8 => word &&& (uint8Modulus - 1)
  | .uint16 => word &&& (2^16 - 1)
  | .uintN bits => word &&& (2 ^ bits - 1)
  | .intN bits =>
      (Verity.Core.Uint256.signextend
        (Verity.Core.Uint256.ofNat (bits / 8 - 1))
        (Verity.Core.Uint256.ofNat word)).val
  | .bytesN bytes =>
      word &&& ((2 ^ (8 * bytes) - 1) * 2 ^ (8 * (32 - bytes)))
  | .address => word &&& Compiler.Constants.addressMask
  | .bool => if word = 0 then 0 else 1
  -- Mirrors the compiler's newtype erasure in `normalizeEventWord`.
  | .newtypeOf _ baseType => normalizeEventValue baseType value
  | _ => word

def splitEventArgsByParams :
    List EventParam → List Nat → Option (List Verity.Core.Uint256 × List Verity.Core.Uint256)
  | [], [] => some ([], [])
  | param :: params, value :: values => do
      let (args, indexedArgs) ← splitEventArgsByParams params values
      let normalized := normalizeEventValue param.ty value
      if param.kind == EventParamKind.indexed then
        some (args, (normalized : Verity.Core.Uint256) :: indexedArgs)
      else
        some ((normalized : Verity.Core.Uint256) :: args, indexedArgs)
  | _, _ => none

theorem exists_splitEventArgsByParams_of_length :
    ∀ {params : List EventParam} {values : List Nat},
      values.length = params.length →
        ∃ args indexedArgs,
          splitEventArgsByParams params values = some (args, indexedArgs)
  | [], [], _ => by
      exact ⟨[], [], rfl⟩
  | [], _ :: _, hlen => by
      simp at hlen
  | _ :: _, [], hlen => by
      simp at hlen
  | param :: params, value :: values, hlen => by
      have htail : values.length = params.length := by
        simpa using Nat.succ.inj hlen
      rcases exists_splitEventArgsByParams_of_length htail with
        ⟨args, indexedArgs, hsplit⟩
      by_cases hkind : param.kind == EventParamKind.indexed
      · exact ⟨args, (normalizeEventValue param.ty value : Verity.Core.Uint256) :: indexedArgs,
          by simp [splitEventArgsByParams, hsplit, hkind]⟩
      · exact ⟨(normalizeEventValue param.ty value : Verity.Core.Uint256) :: args, indexedArgs,
          by simp [splitEventArgsByParams, hsplit, hkind]⟩

def eventFromResolvedArgs? (events : List EventDef) (eventName : String)
    (values : List Nat) : Option Verity.Event :=
  match events.find? (·.name == eventName) with
  | none =>
      some { name := eventName, args := valuesAsEventArgs values, indexedArgs := [] }
  | some eventDef => do
      let (args, indexedArgs) ← splitEventArgsByParams eventDef.params values
      some {
        name := eventName
        args := args
        indexedArgs := (eventSignatureTopic eventDef : Verity.Core.Uint256) :: indexedArgs }

theorem exists_eventFromResolvedArgs?_of_supported_length
    {events : List EventDef}
    {eventName : String}
    {exprArgs : List Expr}
    {values : List Nat}
    (hsupport : eventEmissionProofSupported events eventName exprArgs = true)
    (hlen : values.length = exprArgs.length) :
    ∃ event, eventFromResolvedArgs? events eventName values = some event := by
  rcases exists_eventDef_of_eventEmissionProofSupported hsupport with
    ⟨eventDef, hfind, _hscalar, hargsLen⟩
  have hvalueLen : values.length = eventDef.params.length := by
    rw [hlen, hargsLen]
  rcases exists_splitEventArgsByParams_of_length hvalueLen with
    ⟨args, indexedArgs, hsplit⟩
  refine ⟨{ name := eventName
            args := args
            indexedArgs :=
              (eventSignatureTopic eventDef : Verity.Core.Uint256) :: indexedArgs }, ?_⟩
  simp [eventFromResolvedArgs?, hfind, hsplit]

/-- Sequential scratch stores of the signature chunk words, starting at word
index `wordIdx`. Write keys wrap mod `2^256`, mirroring the compiled code's
wrapping `add` offset arithmetic. -/
def writeEventSignatureScratchFrom :
    List Nat → Nat → Nat → (Nat → Verity.Core.Uint256) → (Nat → Verity.Core.Uint256)
  | [], _, _, memory => memory
  | word :: words, ptr, wordIdx, memory =>
      writeEventSignatureScratchFrom words ptr (wordIdx + 1)
        (fun offset =>
          if offset = (ptr + wordIdx * 32) % Compiler.Constants.evmModulus then
            (word : Verity.Core.Uint256)
          else
            memory offset)

def writeEventSignatureScratch (eventDef : EventDef)
    (ptr : Nat) (memory : Nat → Verity.Core.Uint256) : Nat → Verity.Core.Uint256 :=
  writeEventSignatureScratchFrom
    ((chunkBytes32 (bytesFromString (eventSignature eventDef))).map wordFromBytes)
    ptr 0 memory

def writeUnindexedEventScratchFrom :
    List EventParam → List Nat → Nat → Nat → (Nat → Verity.Core.Uint256) →
      Option (Nat → Verity.Core.Uint256)
  | [], [], _, _, memory => some memory
  | param :: params, value :: values, ptr, wordIdx, memory =>
      let normalized := normalizeEventValue param.ty value
      let next :=
        if param.kind == EventParamKind.unindexed then
          fun offset =>
            if offset = (ptr + wordIdx * 32) % Compiler.Constants.evmModulus then
              (normalized : Verity.Core.Uint256)
            else
              memory offset
        else
          memory
      writeUnindexedEventScratchFrom params values ptr
        (if param.kind == EventParamKind.unindexed then wordIdx + 1 else wordIdx)
        next
  | _, _, _, _, _ => none

def writeUnindexedEventScratch
    (params : List EventParam) (values : List Nat)
    (ptr : Nat) (memory : Nat → Verity.Core.Uint256) : Option (Nat → Verity.Core.Uint256) :=
  writeUnindexedEventScratchFrom params values ptr 0 memory

theorem exists_writeUnindexedEventScratch_of_length :
    ∀ {params : List EventParam} {values : List Nat}
      {ptr wordIdx : Nat} {memory : Nat → Verity.Core.Uint256},
      values.length = params.length →
        ∃ memory',
          writeUnindexedEventScratchFrom params values ptr wordIdx memory = some memory'
  | [], [], _, _, memory, _ => by
      exact ⟨memory, rfl⟩
  | [], _ :: _, _, _, _, hlen => by
      simp at hlen
  | _ :: _, [], _, _, _, hlen => by
      simp at hlen
  | param :: params, value :: values, ptr, wordIdx, memory, hlen => by
      have htail : values.length = params.length := by
        simpa using Nat.succ.inj hlen
      by_cases hkind : param.kind == EventParamKind.unindexed
      · rcases exists_writeUnindexedEventScratch_of_length
            (params := params) (values := values) (ptr := ptr)
            (wordIdx := wordIdx + 1)
            (memory := fun offset =>
              if offset = (ptr + wordIdx * 32) % Compiler.Constants.evmModulus then
                (normalizeEventValue param.ty value : Verity.Core.Uint256)
              else
                memory offset)
            htail with
          ⟨memory', hmem⟩
        refine ⟨memory', ?_⟩
        simpa [writeUnindexedEventScratchFrom, hkind] using hmem
      · rcases exists_writeUnindexedEventScratch_of_length
            (params := params) (values := values) (ptr := ptr)
            (wordIdx := wordIdx)
            (memory := memory)
            htail with
          ⟨memory', hmem⟩
        refine ⟨memory', ?_⟩
        simpa [writeUnindexedEventScratchFrom, hkind] using hmem

theorem exists_writeUnindexedEventScratch_of_length_zero
    {params : List EventParam} {values : List Nat}
    {ptr : Nat} {memory : Nat → Verity.Core.Uint256}
    (hlen : values.length = params.length) :
    ∃ memory', writeUnindexedEventScratch params values ptr memory = some memory' := by
  simpa [writeUnindexedEventScratch] using
    (exists_writeUnindexedEventScratch_of_length
      (params := params) (values := values) (ptr := ptr) (wordIdx := 0)
      (memory := memory) hlen)

def eventScratchMemoryAfterEmit? (events : List EventDef)
    (eventName : String) (values : List Nat)
    (memory : Nat → Verity.Core.Uint256) : Option (Nat → Verity.Core.Uint256) :=
  match events.find? (·.name == eventName) with
  | none => some memory
  | some eventDef =>
      if eventDefScalarProofSupported eventDef then
        let ptr := (memory Compiler.Constants.freeMemoryPointer).val
        writeUnindexedEventScratch eventDef.params values ptr
          (writeEventSignatureScratch eventDef ptr memory)
      else
        some memory

theorem exists_eventScratchMemoryAfterEmit?_of_supported_length
    {events : List EventDef}
    {eventName : String}
    {exprArgs : List Expr}
    {values : List Nat}
    {memory : Nat → Verity.Core.Uint256}
    (hsupport : eventEmissionProofSupported events eventName exprArgs = true)
    (hlen : values.length = exprArgs.length) :
    ∃ memory',
      eventScratchMemoryAfterEmit? events eventName values memory = some memory' := by
  rcases exists_eventDef_of_eventEmissionProofSupported hsupport with
    ⟨eventDef, hfind, hscalar, hargsLen⟩
  have hvalueLen : values.length = eventDef.params.length := by
    rw [hlen, hargsLen]
  unfold eventScratchMemoryAfterEmit?
  simp [hfind, hscalar]
  exact exists_writeUnindexedEventScratch_of_length_zero
    (params := eventDef.params) (values := values)
    (ptr := (memory Compiler.Constants.freeMemoryPointer).val)
    (memory := writeEventSignatureScratch eventDef
      (memory Compiler.Constants.freeMemoryPointer).val memory)
    hvalueLen

def effectiveFields (spec : CompilationModel) : List Field :=
  applySlotAliasRanges spec.fields spec.slotAliasRanges

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

def findDynamicArrayElementAtSlot
    (fields : List Field) (world : Verity.ContractState) (targetSlot : Nat) : Option Nat :=
  let rec scanElements (baseSlot : Nat) : List Verity.Core.Uint256 → Nat → Option Nat
    | [], _ => none
    | value :: rest, idx =>
        if Compiler.Proofs.solidityMappingSlot baseSlot idx = wordNormalize targetSlot then
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
            match scanElements resolvedSlot (world.storageArray resolvedSlot) 0 with
            | some value => some value
            | none => go rest (idx + 1)
        | _ => go rest (idx + 1)
  go fields 0

/-- Bridge lemma: the EvmYulLean `UInt256.size` and the verity-core
`UINT256_MODULUS` literal are the same `Nat` (`2^256`). Used to discharge
`% UInt256.size` modulo wraps that arise from `IRStorageWord.toNat`
projection of values originally bounded by `Verity.Core.Uint256.isLt`. -/
@[simp] theorem UInt256_size_eq_UINT256_MODULUS :
    EvmYul.UInt256.size = Verity.Core.UINT256_MODULUS := by
  unfold EvmYul.UInt256.size Verity.Core.UINT256_MODULUS
  rfl

def encodeStorageAt (fields : List Field) (world : Verity.ContractState) (slot : Nat) : Nat :=
  match findResolvedFieldAtSlot fields slot with
  | some field =>
      if fieldUsesAddressStorage field then
        (world.storageAddr slot).val
      else if fieldUsesDynamicArrayStorage field then
        (world.storageArray slot).length
      else
        (world.storage slot).val
  | none =>
      match findDynamicArrayElementAtSlot fields world slot with
      | some value => value
      | none => (world.storage slot).val

def encodeStorage (spec : CompilationModel) (world : Verity.ContractState) :
    Nat → Nat :=
  encodeStorageAt (effectiveFields spec) world

def writeUintSlots (world : Verity.ContractState) (slots : List Nat) (value : Nat) :
    Verity.ContractState :=
  let word : Verity.Core.Uint256 := value
  let targets := slots.map wordNormalize
  world.writeSlots targets word

def writeStorageWordSlot (world : Verity.ContractState) (slot wordOffset value : Nat) :
    Verity.ContractState :=
  let word : Verity.Core.Uint256 := value
  let addr := Verity.wordToAddress word
  let target := wordNormalize (slot + wordOffset)
  (world.writeSlot target word).writeAddrSlot target addr

def writeStorageWordSlots (world : Verity.ContractState) (slots : List Nat) (wordOffset value : Nat) :
    Verity.ContractState :=
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
    world.transientStorage (wordNormalize slot)
  else
    world.storage (wordNormalize slot)

def writeTransientTargets (world : Verity.ContractState) (targets : List Nat) (value : Nat) :
    Verity.ContractState :=
  let word : Verity.Core.Uint256 := value
  let targets := targets.map wordNormalize
  world.writeTransientSlots targets word

def packedWordWrite (current value : Nat) (packed : PackedBits) : Nat :=
  let maskNat := packedMaskNat packed
  let shiftedMaskNat := packedShiftedMaskNat packed
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
    world.writeSlots (targets.map wordNormalize) (value : Verity.Core.Uint256)

def writeAddressKeyedMappingSlots
    (world : Verity.ContractState) (slots : List Nat) (key value : Nat) :
    Verity.ContractState :=
  match slots with
  | [] => world
  | slot :: _ =>
      let keyAddr := Verity.wordToAddress (key : Verity.Core.Uint256)
      let word : Verity.Core.Uint256 := value
      let storageNat : Compiler.Proofs.IRGeneration.IRStorageSlot →
          Compiler.Proofs.IRGeneration.IRStorageWord :=
        fun s => Compiler.Proofs.IRGeneration.IRStorageWord.ofNat (world.storage s.toNat).val
      let storage :=
        slots.foldl
          (fun current slot =>
            Compiler.Proofs.abstractStoreMappingEntry current slot key value)
        storageNat
      (world.withStorageChannel (fun _ s =>
        (Compiler.Proofs.IRGeneration.IRStorageWord.toNat
          (storage (Compiler.Proofs.IRGeneration.IRStorageSlot.ofNat s)) : Verity.Core.Uint256))).writeMap
        slot keyAddr word

def mappingSlotChain (baseSlot : Nat) (keys : List Nat) : Nat :=
  keys.foldl Compiler.Proofs.abstractMappingSlot baseSlot

def writeAddressKeyedMappingChainSlots
    (world : Verity.ContractState) (slots keys : List Nat) (value : Nat) :
    Verity.ContractState :=
  let word : Verity.Core.Uint256 := value
  let targets := slots.map (fun slot => wordNormalize (mappingSlotChain slot keys))
  world.writeSlots targets word

def writeAddressKeyedMappingWordSlots
    (world : Verity.ContractState) (slots : List Nat) (key wordOffset value : Nat) :
    Verity.ContractState :=
  let word : Verity.Core.Uint256 := value
  let targets :=
    slots.map (fun slot =>
      wordNormalize (Compiler.Proofs.abstractMappingSlot slot key + wordOffset))
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
    some (world.modifySlots targets (fun current => packedWordWrite current.val value packed))
  else
    none

def writeAddressKeyedMappingPackedWordSlots
    (world : Verity.ContractState) (slots : List Nat) (key wordOffset : Nat)
    (packed : PackedBits) (value : Nat) :
    Verity.ContractState :=
  let targets :=
    slots.map (fun slot =>
      wordNormalize (Compiler.Proofs.abstractMappingSlot slot key + wordOffset))
  world.modifySlots targets (fun current => packedWordWrite current.val value packed)

def writeAddressKeyedMappingPackedWordFieldSlots
    (fields : List Field) (fieldName : String)
    (world : Verity.ContractState) (slots : List Nat) (key wordOffset : Nat)
    (packed : PackedBits) (value : Nat) :
    Verity.ContractState :=
  let targets :=
    slots.map (fun slot =>
      wordNormalize (Compiler.Proofs.abstractMappingSlot slot key + wordOffset))
  if fieldIsTransient fields fieldName then
    world.modifyTransientSlots targets (fun current => packedWordWrite current.val value packed)
  else
    writeAddressKeyedMappingPackedWordSlots world slots key wordOffset packed value

def writeAddressKeyedMapping2PackedWordSlots
    (world : Verity.ContractState) (slots : List Nat) (key1 key2 wordOffset : Nat)
    (packed : PackedBits) (value : Nat) :
    Verity.ContractState :=
  let targets :=
    slots.map (fun slot =>
      wordNormalize
        (Compiler.Proofs.abstractMappingSlot
          (Compiler.Proofs.abstractMappingSlot slot key1) key2 + wordOffset))
  world.modifySlots targets (fun current => packedWordWrite current.val value packed)

def writeAddressKeyedMapping2PackedWordFieldSlots
    (fields : List Field) (fieldName : String)
    (world : Verity.ContractState) (slots : List Nat) (key1 key2 wordOffset : Nat)
    (packed : PackedBits) (value : Nat) :
    Verity.ContractState :=
  let targets :=
    slots.map (fun slot =>
      wordNormalize
        (Compiler.Proofs.abstractMappingSlot
          (Compiler.Proofs.abstractMappingSlot slot key1) key2 + wordOffset))
  if fieldIsTransient fields fieldName then
    world.modifyTransientSlots targets (fun current => packedWordWrite current.val value packed)
  else
    writeAddressKeyedMapping2PackedWordSlots world slots key1 key2 wordOffset packed value

def writeUintKeyedMappingSlots
    (world : Verity.ContractState) (slots : List Nat) (key value : Nat) :
    Verity.ContractState :=
  match slots with
  | [] => world
  | slot :: _ =>
      let keyWord : Verity.Core.Uint256 := key
      let word : Verity.Core.Uint256 := value
      let storageNat : Compiler.Proofs.IRGeneration.IRStorageSlot →
          Compiler.Proofs.IRGeneration.IRStorageWord :=
        fun s => Compiler.Proofs.IRGeneration.IRStorageWord.ofNat (world.storage s.toNat).val
      let storage :=
        slots.foldl
          (fun current slot =>
            Compiler.Proofs.abstractStoreMappingEntry current slot key value)
        storageNat
      (world.withStorageChannel (fun _ s =>
        (Compiler.Proofs.IRGeneration.IRStorageWord.toNat
          (storage (Compiler.Proofs.IRGeneration.IRStorageSlot.ofNat s)) : Verity.Core.Uint256))).writeMapUint
        slot keyWord word

def writeAddressKeyedMapping2Slots
    (world : Verity.ContractState) (slots : List Nat) (key1 key2 value : Nat) :
    Verity.ContractState :=
  match slots with
  | [] => world
  | slot :: _ =>
      let key1Addr := Verity.wordToAddress (key1 : Verity.Core.Uint256)
      let key2Addr := Verity.wordToAddress (key2 : Verity.Core.Uint256)
      let word : Verity.Core.Uint256 := value
      let storageNat : Compiler.Proofs.IRGeneration.IRStorageSlot →
          Compiler.Proofs.IRGeneration.IRStorageWord :=
        fun s => Compiler.Proofs.IRGeneration.IRStorageWord.ofNat (world.storage s.toNat).val
      let storage :=
        slots.foldl
          (fun current slot =>
            Compiler.Proofs.abstractStoreMappingEntry
              current
              (Compiler.Proofs.abstractMappingSlot slot key1)
              key2
              value)
        storageNat
      (world.withStorageChannel (fun _ s =>
        (Compiler.Proofs.IRGeneration.IRStorageWord.toNat
          (storage (Compiler.Proofs.IRGeneration.IRStorageSlot.ofNat s)) : Verity.Core.Uint256))).writeMap2
        slot key1Addr key2Addr word

def writeAddressKeyedMapping2WordSlots
    (world : Verity.ContractState) (slots : List Nat) (key1 key2 wordOffset value : Nat) :
    Verity.ContractState :=
  let word : Verity.Core.Uint256 := value
  let targets := slots.map (fun slot =>
    wordNormalize
      (Compiler.Proofs.abstractMappingSlot
        (Compiler.Proofs.abstractMappingSlot slot key1)
        key2 + wordOffset))
  world.writeSlots targets word

def writeAddressKeyedMappingWordFieldSlots
    (fields : List Field) (fieldName : String)
    (world : Verity.ContractState) (slots : List Nat) (key wordOffset value : Nat) :
    Verity.ContractState :=
  let targets :=
    slots.map (fun slot =>
      wordNormalize (Compiler.Proofs.abstractMappingSlot slot key + wordOffset))
  writeMappingTargets fields fieldName world targets value

def writeAddressKeyedMappingFieldSlots
    (fields : List Field) (fieldName : String)
    (world : Verity.ContractState) (slots : List Nat) (key value : Nat) :
    Verity.ContractState :=
  if fieldIsTransient fields fieldName then
    let targets :=
      slots.map (fun slot =>
        wordNormalize (Compiler.Proofs.abstractMappingSlot slot key))
    writeTransientTargets world targets value
  else
    writeAddressKeyedMappingSlots world slots key value

def writeAddressKeyedMappingChainFieldSlots
    (fields : List Field) (fieldName : String)
    (world : Verity.ContractState) (slots keys : List Nat) (value : Nat) :
    Verity.ContractState :=
  if fieldIsTransient fields fieldName then
    let targets :=
      slots.map (fun slot =>
        wordNormalize (keys.foldl Compiler.Proofs.abstractMappingSlot slot))
    writeTransientTargets world targets value
  else
    writeAddressKeyedMappingChainSlots world slots keys value

def writeAddressKeyedMapping2WordFieldSlots
    (fields : List Field) (fieldName : String)
    (world : Verity.ContractState) (slots : List Nat) (key1 key2 wordOffset value : Nat) :
    Verity.ContractState :=
  let targets := slots.map (fun slot =>
    wordNormalize
      (Compiler.Proofs.abstractMappingSlot
        (Compiler.Proofs.abstractMappingSlot slot key1)
        key2 + wordOffset))
  writeMappingTargets fields fieldName world targets value

def writeUintKeyedMappingFieldSlots
    (fields : List Field) (fieldName : String)
    (world : Verity.ContractState) (slots : List Nat) (key value : Nat) :
    Verity.ContractState :=
  if fieldIsTransient fields fieldName then
    let targets :=
      slots.map (fun slot =>
        wordNormalize (Compiler.Proofs.abstractMappingSlot slot key))
    writeTransientTargets world targets value
  else
    writeUintKeyedMappingSlots world slots key value

def writeAddressKeyedMapping2FieldSlots
    (fields : List Field) (fieldName : String)
    (world : Verity.ContractState) (slots : List Nat) (key1 key2 value : Nat) :
    Verity.ContractState :=
  if fieldIsTransient fields fieldName then
    let targets := slots.map (fun slot =>
      wordNormalize
        (Compiler.Proofs.abstractMappingSlot
          (Compiler.Proofs.abstractMappingSlot slot key1)
          key2))
    writeTransientTargets world targets value
  else
    writeAddressKeyedMapping2Slots world slots key1 key2 value

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

def bindValue (bindings : List (String × Nat)) (name : String) (value : Nat) :
    List (String × Nat) :=
  (name, value) :: bindings.filter (fun entry => entry.1 != name)

def bindValues (bindings : List (String × Nat)) : List String → List Nat → List (String × Nat)
  | [], _ => bindings
  | _ :: _, [] => bindings
  | name :: names, value :: values => bindValues (bindValue bindings name value) names values

def lookupValue (bindings : List (String × Nat)) (name : String) : Nat :=
  bindings.find? (fun entry => entry.1 == name) |>.map Prod.snd |>.getD 0

def lookupBinding? (bindings : List (String × Nat)) (name : String) : Option Nat :=
  bindings.find? (fun entry => entry.1 == name) |>.map Prod.snd

private theorem findEntry_filter_ne_eq_findEntry
    (entries : List (String × Nat))
    (blockedName queryName : String)
    (hNe : queryName ≠ blockedName) :
    List.find? (fun entry => entry.1 == queryName)
        (entries.filter (fun entry => entry.1 != blockedName)) =
      List.find? (fun entry => entry.1 == queryName) entries := by
  induction entries with
  | nil =>
      simp
  | cons entry rest ih =>
      by_cases hBlocked : entry.1 = blockedName
      · subst hBlocked
        have hHeadNe : entry.1 ≠ queryName := by
          intro hHeadEq
          apply hNe
          simp [hHeadEq]
        simp [hHeadNe, ih]
      · by_cases hQuery : entry.1 = queryName
        · subst hQuery
          simp [hBlocked]
        · simp [hBlocked, hQuery, ih]

theorem lookupBinding?_bindValue_ne
    (bindings : List (String × Nat))
    (boundName queryName : String)
    (value : Nat)
    (hNe : queryName ≠ boundName) :
    lookupBinding?
      (bindValue bindings boundName value)
      queryName =
    lookupBinding? bindings queryName := by
  have hNe' : boundName ≠ queryName := by
    intro hEq
    apply hNe
    simp [hEq]
  calc
    lookupBinding?
        (bindValue bindings boundName value)
        queryName
        =
          Option.map Prod.snd
            (List.find? (fun entry => entry.1 == queryName)
              ((boundName, value) :: List.filter (fun entry => entry.1 != boundName) bindings)) := by
                rfl
    _ = Option.map Prod.snd
          (List.find? (fun entry => entry.1 == queryName)
            (List.filter (fun entry => entry.1 != boundName) bindings)) := by
              simp [hNe']
    _ = Option.map Prod.snd
          (List.find? (fun entry => entry.1 == queryName) bindings) := by
              rw [findEntry_filter_ne_eq_findEntry bindings boundName queryName hNe]
    _ = lookupBinding? bindings queryName := by
          rfl

theorem lookupBinding?_bindValue_exists
    (bindings : List (String × Nat))
    (boundName queryName : String)
    (value : Nat)
    (hexists : ∃ found, lookupBinding? bindings queryName = some found) :
    ∃ found, lookupBinding? (bindValue bindings boundName value) queryName = some found := by
  by_cases hEq : queryName = boundName
  · subst hEq
    exact ⟨value, by simp [lookupBinding?, bindValue]⟩
  · rcases hexists with ⟨found, hfound⟩
    exact ⟨found, by rw [lookupBinding?_bindValue_ne bindings boundName queryName value hEq, hfound]⟩

def bindInternalArgs (params : List Param) (args : List Nat) :
    Option (List (String × Nat)) :=
  match params, args with
  | [], [] => some []
  | param :: restParams, arg :: restArgs => do
      let bindings ← bindInternalArgs restParams restArgs
      pure ((param.name, arg) :: bindings)
  | _, _ => none

private def findUniqueInternalFunction? (spec : CompilationModel) (calleeName : String) :
    Option FunctionSpec :=
  match spec.functions.filter (fun fn => fn.isInternal && fn.name == calleeName) with
  | [fn] => some fn
  | _ => none

structure ExternalCallOutcome where
  succeeded : Bool
  returnValues : List Nat := []
  postCallWorld : Option Verity.ContractState := none

instance : Inhabited ExternalCallOutcome := ⟨⟨false, [], none⟩⟩

/-- Install the EIP-211 returndata buffer left by a call receipt. The callee's
    return data replaces the buffer wholesale on both the success and the
    failure path, which is what lets the compiled `returndatacopy(0, 0,
    returndatasize())` idiom bubble a callee revert reason. -/
def returndataAfterCall (outcome : ExternalCallOutcome)
    (world : Verity.ContractState) : Verity.ContractState :=
  { world with returndata := outcome.returnValues.map wordNormalize }

@[simp] theorem returndataAfterCall_returndata
    (outcome : ExternalCallOutcome) (world : Verity.ContractState) :
    (returndataAfterCall outcome world).returndata
      = outcome.returnValues.map wordNormalize := rfl

structure RuntimeState where
  world : Verity.ContractState
  immutable : String → Verity.Core.Uint256 := fun _ => 0
  bindings : List (String × Nat)
  selector : Nat := 0
  externalCallOracle : Nat → ExternalCallOutcome := fun _ => ⟨false, [], none⟩
  externalCallIndex : Nat := 0

inductive StmtResult where
  | continue (state : RuntimeState)
  | stop (state : RuntimeState)
  | return (value : Nat) (state : RuntimeState)
  | revert

def execForEachLoop
    (varName : String)
    (runBody : RuntimeState → StmtResult) :
    RuntimeState → Nat → Nat → StmtResult
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
    (runBody : RuntimeState → StmtResult) :
    Nat → RuntimeState → Nat → StmtResult
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

@[simp] theorem execForEachSetBitLoop_zero
    (varName : String)
    (runBody : RuntimeState → StmtResult)
    (state : RuntimeState)
    (bitmap : Nat) :
    execForEachSetBitLoop varName runBody 0 state bitmap = .continue state := rfl

theorem execForEachSetBitLoop_succ
    (varName : String)
    (runBody : RuntimeState → StmtResult)
    (fuel : Nat)
    (state : RuntimeState)
    (bitmap : Nat) :
    execForEachSetBitLoop varName runBody (fuel + 1) state bitmap =
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
        | .revert => .revert := rfl

@[simp] theorem execForEachLoop_zero
    (varName : String)
    (runBody : RuntimeState → StmtResult)
    (state : RuntimeState)
    (index : Nat) :
    execForEachLoop varName runBody state index 0 = .continue state := rfl

theorem execForEachLoop_succ
    (varName : String)
    (runBody : RuntimeState → StmtResult)
    (state : RuntimeState)
    (index remaining : Nat) :
    execForEachLoop varName runBody state index (remaining + 1) =
      let loopState :=
        { state with bindings := bindValue state.bindings varName (wordNormalize index) }
      match runBody loopState with
      | .continue next => execForEachLoop varName runBody next (index + 1) remaining
      | .stop next => .stop next
      | .return value next => .return value next
      | .revert => .revert := rfl

@[simp] theorem lookupBinding?_bindValue_same
    (bindings : List (String × Nat))
    (name : String)
    (value : Nat) :
    lookupBinding? (bindValue bindings name value) name = some value := by
  simp [lookupBinding?, bindValue]

@[simp] theorem lookupValue_bindValue_same
    (bindings : List (String × Nat))
    (name : String)
    (value : Nat) :
    lookupValue (bindValue bindings name value) name = value := by
  simp [lookupValue, bindValue]

@[simp] theorem execForEachLoop_boundState_lookupBinding?
    (varName : String)
    (state : RuntimeState)
    (index : Nat) :
    lookupBinding?
        (bindValue state.bindings varName (wordNormalize index))
        varName =
      some (wordNormalize index) := by
  simp

@[simp] theorem execForEachLoop_boundState_lookupValue
    (varName : String)
    (state : RuntimeState)
    (index : Nat) :
    lookupValue
        (bindValue state.bindings varName (wordNormalize index))
        varName =
      wordNormalize index := by
  simp

theorem execForEachLoop_zero_continue_state
    {varName : String}
    {runBody : RuntimeState → StmtResult}
    {state final : RuntimeState}
    {index : Nat}
    (hloop : execForEachLoop varName runBody state index 0 = .continue final) :
    final = state := by
  simpa [execForEachLoop] using hloop.symm

theorem execForEachLoop_succ_continue_iff
    {varName : String}
    {runBody : RuntimeState → StmtResult}
    {state final : RuntimeState}
    {index remaining : Nat} :
    execForEachLoop varName runBody state index (remaining + 1) = .continue final ↔
      ∃ next,
        runBody
            { state with
              bindings := bindValue state.bindings varName (wordNormalize index) } =
          .continue next ∧
        execForEachLoop varName runBody next (index + 1) remaining =
          .continue final := by
  simp only [execForEachLoop]
  cases hbody :
      runBody
        { state with
          bindings := bindValue state.bindings varName (wordNormalize index) } <;>
    simp [hbody]

theorem execForEachLoop_succ_continue
    {varName : String}
    {runBody : RuntimeState → StmtResult}
    {state next final : RuntimeState}
    {index remaining : Nat}
    (hbody :
      runBody
          { state with
            bindings := bindValue state.bindings varName (wordNormalize index) } =
        .continue next)
    (hloop :
      execForEachLoop varName runBody next (index + 1) remaining =
        .continue final) :
    execForEachLoop varName runBody state index (remaining + 1) =
      .continue final := by
  rw [execForEachLoop_succ]
  simpa only [hbody] using hloop

theorem execForEachLoop_congr
    {varName : String}
    {runBodyA runBodyB : RuntimeState → StmtResult}
    (hbody : ∀ state, runBodyA state = runBodyB state) :
    ∀ (state : RuntimeState) (index remaining : Nat),
      execForEachLoop varName runBodyA state index remaining =
        execForEachLoop varName runBodyB state index remaining
  | state, index, 0 => by
      simp [execForEachLoop]
  | state, index, remaining + 1 => by
      simp only [execForEachLoop]
      rw [hbody]
      cases hrun : runBodyB
        { state with bindings := bindValue state.bindings varName (wordNormalize index) } <;>
        simp [hrun, execForEachLoop_congr hbody]

theorem execForEachSetBitLoop_congr
    {varName : String}
    {runBodyA runBodyB : RuntimeState → StmtResult}
    (hbody : ∀ state, runBodyA state = runBodyB state) :
    ∀ (fuel : Nat) (state : RuntimeState) (bitmap : Nat),
      execForEachSetBitLoop varName runBodyA fuel state bitmap =
        execForEachSetBitLoop varName runBodyB fuel state bitmap
  | 0, state, bitmap => by
      simp [execForEachSetBitLoop]
  | fuel + 1, state, bitmap => by
      simp only [execForEachSetBitLoop]
      by_cases hbitmap : bitmap = 0
      · simp [hbitmap]
      · simp [hbitmap]
        rw [hbody]
        cases hrun : runBodyB
          { state with bindings := bindValue state.bindings varName (wordNormalize (msbIndex bitmap)) } <;>
          simp [hrun, execForEachSetBitLoop_congr hbody]

def execForEachEmptyLoopFinal
    (varName : String) : RuntimeState → Nat → Nat → RuntimeState
  | state, _, 0 => state
  | state, index, remaining + 1 =>
      execForEachEmptyLoopFinal varName
        { state with bindings := bindValue state.bindings varName (wordNormalize index) }
        (index + 1) remaining

theorem execForEachLoop_empty_body
    (varName : String)
    (state : RuntimeState)
    (index remaining : Nat) :
    execForEachLoop varName (fun loopState => .continue loopState)
        state index remaining =
      .continue (execForEachEmptyLoopFinal varName state index remaining) := by
  induction remaining generalizing state index with
  | zero =>
      rfl
  | succ remaining ih =>
      simp [execForEachLoop, execForEachEmptyLoopFinal, ih]

theorem execForEachLoop_empty_body_zero_bound
    (varName : String)
    (state : RuntimeState)
    (index : Nat) :
    execForEachLoop varName (fun loopState => .continue loopState)
        state index 0 =
      .continue state := rfl

theorem execForEachLoop_empty_body_positive_bound
    (varName : String)
    (state : RuntimeState)
    (index remaining : Nat) :
    execForEachLoop varName (fun loopState => .continue loopState)
        state index (remaining + 1) =
      .continue
        (execForEachEmptyLoopFinal varName
          { state with bindings := bindValue state.bindings varName (wordNormalize index) }
          (index + 1) remaining) := by
  simp [execForEachLoop_empty_body, execForEachEmptyLoopFinal]

def storageArraySetAt : List Verity.Core.Uint256 → Nat → Verity.Core.Uint256 → Option (List Verity.Core.Uint256)
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

/-- Ceiling-division helper matching Solidity's `Math256.ceilDiv`.
    Factored out so the mutual block's equation-lemma derivation stays simple. -/
private def ceilDivVal (lhs rhs : Verity.Core.Uint256) : Nat :=
  if lhs == 0 then 0 else ((lhs - 1) / rhs + 1).val

abbrev dynamicArrayBinding? :=
  DynamicAbi.dynamicArrayBinding?

private abbrev arrayElement? :=
  DynamicAbi.arrayElement?

private abbrev arrayElementDynamicHeadOffset? :=
  DynamicAbi.arrayElementDynamicHeadOffset?

private abbrev arrayElementDynamicWord? :=
  DynamicAbi.arrayElementDynamicWord?

private abbrev arrayElementDynamicMemberLength? :=
  DynamicAbi.arrayElementDynamicMemberLength?

private abbrev arrayElementDynamicMemberDataOffset? :=
  DynamicAbi.arrayElementDynamicMemberDataOffset?

private abbrev arrayElementDynamicMemberElement? :=
  DynamicAbi.arrayElementDynamicMemberElement?

def evalExpr (fields : List Field) (state : RuntimeState) : Expr → Option Nat
  | .memoryArrayLength name =>
      lookupBinding? state.bindings s!"{name}_length"
  | .memoryArrayElement name index => do
      let idx ← evalExpr fields state index
      let (dataOffset, length) ← dynamicArrayBinding? state.bindings name
      if idx < length then
        some (state.world.memory (wordNormalize (dataOffset + 32 * idx))).val
      else
        none
  | .arrayLength name =>
      lookupBinding? state.bindings s!"{name}_length"
  | .arrayElement name index => do
      let idx ← evalExpr fields state index
      let (dataOffset, length) ← dynamicArrayBinding? state.bindings name
      arrayElement? state.selector state.world.calldata dataOffset length idx
  | .dynamicBytesEq lhsName rhsName => do
      let (lhsOffset, lhsLength) ← dynamicArrayBinding? state.bindings lhsName
      let (rhsOffset, rhsLength) ← dynamicArrayBinding? state.bindings rhsName
      some (boolWord (DynamicAbi.dynamicBytesEqCalldata state.selector state.world.calldata
        lhsOffset lhsLength rhsOffset rhsLength))
  | .arrayElementDynamicDataOffset name index => do
      let idx ← evalExpr fields state index
      let (dataOffset, length) ← dynamicArrayBinding? state.bindings name
      arrayElementDynamicHeadOffset? state.selector state.world.calldata dataOffset length idx
  | .arrayElementDynamicMemberLength name index wordOffset => do
      let idx ← evalExpr fields state index
      let (dataOffset, length) ← dynamicArrayBinding? state.bindings name
      arrayElementDynamicMemberLength?
        state.selector state.world.calldata dataOffset length idx wordOffset
  | .arrayElementDynamicMemberDataOffset name index wordOffset => do
      let idx ← evalExpr fields state index
      let (dataOffset, length) ← dynamicArrayBinding? state.bindings name
      arrayElementDynamicMemberDataOffset?
        state.selector state.world.calldata dataOffset length idx wordOffset
  | .arrayElementDynamicMemberElement name index wordOffset innerIndex => do
      let idx ← evalExpr fields state index
      let innerIdx ← evalExpr fields state innerIndex
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
            some (state.world.transientStorage (wordNormalize slot)).val
          else
            some (state.world.storageAddr (wordNormalize slot)).val
      | none => none
  | .storageArrayLength fieldName =>
      match findFieldWithResolvedSlot fields fieldName with
      | some ({ ty := .dynamicArray _, .. }, slot) => some (state.world.storageArray slot).length
      | _ => none
  | .storageArrayElement fieldName index => do
      let idx ← evalExpr fields state index
      match findFieldWithResolvedSlot fields fieldName with
      | some ({ ty := .dynamicArray _, .. }, slot) =>
          match (state.world.storageArray slot)[idx]? with
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
  | .returndataSize => some state.world.returndataSize
  | .localVar name => some (lookupValue state.bindings name)
  | .add a b => do
      let lhs : Verity.Core.Uint256 := ← evalExpr fields state a
      let rhs : Verity.Core.Uint256 := ← evalExpr fields state b
      pure (lhs + rhs).val
  | .sub a b => do
      let lhs : Verity.Core.Uint256 := ← evalExpr fields state a
      let rhs : Verity.Core.Uint256 := ← evalExpr fields state b
      pure (lhs - rhs).val
  | .mul a b => do
      let lhs : Verity.Core.Uint256 := ← evalExpr fields state a
      let rhs : Verity.Core.Uint256 := ← evalExpr fields state b
      pure (lhs * rhs).val
  | .div a b => do
      let lhs : Verity.Core.Uint256 := ← evalExpr fields state a
      let rhs : Verity.Core.Uint256 := ← evalExpr fields state b
      pure (lhs / rhs).val
  | .mod a b => do
      let lhs : Verity.Core.Uint256 := ← evalExpr fields state a
      let rhs : Verity.Core.Uint256 := ← evalExpr fields state b
      pure (lhs % rhs).val
  | .bitAnd a b => do
      let lhs ← evalExpr fields state a
      let rhs ← evalExpr fields state b
      pure (Verity.Core.Uint256.and lhs rhs).val
  | .bitOr a b => do
      let lhs ← evalExpr fields state a
      let rhs ← evalExpr fields state b
      pure (Verity.Core.Uint256.or lhs rhs).val
  | .bitXor a b => do
      let lhs ← evalExpr fields state a
      let rhs ← evalExpr fields state b
      pure (Verity.Core.Uint256.xor lhs rhs).val
  | .bitNot a => do
      let value ← evalExpr fields state a
      pure (Verity.Core.Uint256.not value).val
  | .eq a b => do
      let lhs ← evalExpr fields state a
      let rhs ← evalExpr fields state b
      pure (boolWord (decide (lhs = rhs)))
  | .ge a b => do
      let lhs ← evalExpr fields state a
      let rhs ← evalExpr fields state b
      pure (boolWord (decide (rhs ≤ lhs)))
  | .gt a b => do
      let lhs ← evalExpr fields state a
      let rhs ← evalExpr fields state b
      pure (boolWord (decide (rhs < lhs)))
  | .lt a b => do
      let lhs ← evalExpr fields state a
      let rhs ← evalExpr fields state b
      pure (boolWord (decide (lhs < rhs)))
  | .le a b => do
      let lhs ← evalExpr fields state a
      let rhs ← evalExpr fields state b
      pure (boolWord (decide (lhs ≤ rhs)))
  | .logicalAnd a b => do
      let lhs ← evalExpr fields state a
      let rhs ← evalExpr fields state b
      pure (boolWord (decide (lhs != 0) && decide (rhs != 0)))
  | .logicalOr a b => do
      let lhs ← evalExpr fields state a
      let rhs ← evalExpr fields state b
      pure (boolWord (decide (lhs != 0) || decide (rhs != 0)))
  | .logicalNot a => do
      let value ← evalExpr fields state a
      pure (boolWord (decide (value = 0)))
  | .min a b => do
      let lhs ← evalExpr fields state a
      let rhs ← evalExpr fields state b
      pure (if lhs ≤ rhs then lhs else rhs)
  | .max a b => do
      let lhs ← evalExpr fields state a
      let rhs ← evalExpr fields state b
      pure (if rhs ≤ lhs then lhs else rhs)
  | .wMulDown a b => do
      let lhs : Verity.Core.Uint256 := ← evalExpr fields state a
      let rhs : Verity.Core.Uint256 := ← evalExpr fields state b
      let wad : Verity.Core.Uint256 := 1000000000000000000
      pure ((lhs * rhs) / wad).val
  | .wDivUp a b => do
      let lhs : Verity.Core.Uint256 := ← evalExpr fields state a
      let rhs : Verity.Core.Uint256 := ← evalExpr fields state b
      let wad : Verity.Core.Uint256 := 1000000000000000000
      pure (((lhs * wad) + (rhs - 1)) / rhs).val
  | .ceilDiv a b => do
      let lhs : Verity.Core.Uint256 := ← evalExpr fields state a
      let rhs : Verity.Core.Uint256 := ← evalExpr fields state b
      pure (ceilDivVal lhs rhs)
  | .mulDivDown a b c => do
      let lhs : Verity.Core.Uint256 := ← evalExpr fields state a
      let rhs : Verity.Core.Uint256 := ← evalExpr fields state b
      let denom : Verity.Core.Uint256 := ← evalExpr fields state c
      pure ((lhs * rhs) / denom).val
  | .mulDivUp a b c => do
      let lhs : Verity.Core.Uint256 := ← evalExpr fields state a
      let rhs : Verity.Core.Uint256 := ← evalExpr fields state b
      let denom : Verity.Core.Uint256 := ← evalExpr fields state c
      pure (((lhs * rhs) + (denom - 1)) / denom).val
  | .ite cond thenVal elseVal => do
      let condVal ← evalExpr fields state cond
      if condVal != 0 then
        evalExpr fields state thenVal
      else
        evalExpr fields state elseVal
  | .forkIfAtLeast _ _ _ => none
  | .shl shift value => do
      let shiftVal ← evalExpr fields state shift
      let wordVal ← evalExpr fields state value
      pure (Verity.Core.Uint256.shl shiftVal wordVal).val
  | .shr shift value => do
      let shiftVal ← evalExpr fields state shift
      let wordVal ← evalExpr fields state value
      pure (Verity.Core.Uint256.shr shiftVal wordVal).val
  | .slt a b => do
      let lhs ← evalExpr fields state a
      let rhs ← evalExpr fields state b
      pure (boolWord (decide (
        (Verity.Core.Int256.ofUint256 (Verity.Core.Uint256.ofNat lhs) : Int) <
        (Verity.Core.Int256.ofUint256 (Verity.Core.Uint256.ofNat rhs) : Int))))
  | .sgt a b => do
      let lhs ← evalExpr fields state a
      let rhs ← evalExpr fields state b
      pure (boolWord (decide (
        (Verity.Core.Int256.ofUint256 (Verity.Core.Uint256.ofNat rhs) : Int) <
        (Verity.Core.Int256.ofUint256 (Verity.Core.Uint256.ofNat lhs) : Int))))
  | .sdiv a b => do
      let lhs ← evalExpr fields state a
      let rhs ← evalExpr fields state b
      pure (Verity.Core.Int256.div
        (Verity.Core.Int256.ofUint256 (Verity.Core.Uint256.ofNat lhs))
        (Verity.Core.Int256.ofUint256 (Verity.Core.Uint256.ofNat rhs))).toUint256.val
  | .smod a b => do
      let lhs ← evalExpr fields state a
      let rhs ← evalExpr fields state b
      pure (Verity.Core.Int256.mod
        (Verity.Core.Int256.ofUint256 (Verity.Core.Uint256.ofNat lhs))
        (Verity.Core.Int256.ofUint256 (Verity.Core.Uint256.ofNat rhs))).toUint256.val
  | .sar a b => do
      let lhs ← evalExpr fields state a
      let rhs ← evalExpr fields state b
      pure (Verity.Core.Int256.sar
        (Verity.Core.Int256.ofUint256 (Verity.Core.Uint256.ofNat lhs))
        (Verity.Core.Int256.ofUint256 (Verity.Core.Uint256.ofNat rhs))).toUint256.val
  | .byte a b => do
      let index ← evalExpr fields state a
      let value ← evalExpr fields state b
      pure (Verity.Core.Uint256.byte
        (Verity.Core.Uint256.ofNat index)
        (Verity.Core.Uint256.ofNat value)).val
  | .signextend a b => do
      let byteIdx ← evalExpr fields state a
      let value ← evalExpr fields state b
      pure (Verity.Core.Uint256.signextend
        (Verity.Core.Uint256.ofNat byteIdx)
        (Verity.Core.Uint256.ofNat value)).val
  | .mapping field key => do
      let keyVal ← evalExpr fields state key
      match findFieldWithResolvedSlot fields field with
      | some (field, slot) =>
          some (readFieldWord state.world field (Compiler.Proofs.abstractMappingSlot slot keyVal)).val
      | none => none
  | .mappingWord field key wordOffset => do
      let keyVal ← evalExpr fields state key
      match findFieldWithResolvedSlot fields field with
      | some (field, slot) =>
          some (readFieldWord state.world field
            (wordNormalize (Compiler.Proofs.abstractMappingSlot slot keyVal + wordOffset))).val
      | none => none
  | .mappingUint field key => do
      let keyVal ← evalExpr fields state key
      match findFieldWithResolvedSlot fields field with
      | some (field, slot) =>
          some (readFieldWord state.world field (Compiler.Proofs.abstractMappingSlot slot keyVal)).val
      | none => none
  | .mapping2 field key1 key2 => do
      let key1Val ← evalExpr fields state key1
      let key2Val ← evalExpr fields state key2
      match findFieldWithResolvedSlot fields field with
      | some (field, slot) =>
          let innerSlot := Compiler.Proofs.abstractMappingSlot slot key1Val
          some (readFieldWord state.world field (Compiler.Proofs.abstractMappingSlot innerSlot key2Val)).val
      | none => none
  | .mapping2Word field key1 key2 wordOffset => do
      let key1Val ← evalExpr fields state key1
      let key2Val ← evalExpr fields state key2
      match findFieldWithResolvedSlot fields field with
      | some (field, slot) =>
          let innerSlot := Compiler.Proofs.abstractMappingSlot slot key1Val
          let outerSlot := Compiler.Proofs.abstractMappingSlot innerSlot key2Val
          some (readFieldWord state.world field (wordNormalize (outerSlot + wordOffset))).val
      | none => none
  | .mappingChain field [key] => do
      let keyVal ← evalExpr fields state key
      match findFieldWithResolvedSlot fields field with
      | some (field, slot) =>
          some (readFieldWord state.world field (Compiler.Proofs.abstractMappingSlot slot keyVal)).val
      | none => none
  | .mappingChain field [key1, key2] => do
      let key1Val ← evalExpr fields state key1
      let key2Val ← evalExpr fields state key2
      match findFieldWithResolvedSlot fields field with
      | some (field, slot) =>
          let innerSlot := Compiler.Proofs.abstractMappingSlot slot key1Val
          some (readFieldWord state.world field (Compiler.Proofs.abstractMappingSlot innerSlot key2Val)).val
      | none => none
  -- Longer mappingChain reads remain deferred until the evaluator has shared
  -- list-recursion infrastructure for arbitrary key lists.
  | .structMember field key memberName => do
      let keyVal ← evalExpr fields state key
      match findFieldWithResolvedSlot fields field, findStructMembers fields field with
      | some (fieldInfo, slot), some members =>
          match findStructMember members memberName with
          | some member =>
              let targetSlot := wordNormalize
                (Compiler.Proofs.abstractMappingSlot slot keyVal + member.wordOffset)
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
      let key1Val ← evalExpr fields state key1
      let key2Val ← evalExpr fields state key2
      match findFieldWithResolvedSlot fields field, findStructMembers fields field with
      | some (fieldInfo, slot), some members =>
          match findStructMember members memberName with
          | some member =>
              let innerSlot := Compiler.Proofs.abstractMappingSlot slot key1Val
              let outerSlot := Compiler.Proofs.abstractMappingSlot innerSlot key2Val
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
      let keyVal ← evalExpr fields state key
      match findFieldWithResolvedSlot fields field with
      | some (fieldInfo, slot) =>
          let targetSlot := wordNormalize
            (Compiler.Proofs.abstractMappingSlot slot keyVal + wordOffset)
          let rawWord := (readFieldWord state.world fieldInfo targetSlot).val
          some (Verity.Core.Uint256.and
            (Verity.Core.Uint256.shr packed.offset rawWord)
            (packedMaskNat packed)).val
      | none => none
  | .mload offset => do
      let resolvedOffset ← evalExpr fields state offset
      some (state.world.memory resolvedOffset).val
  | .tload offset => do
      let resolvedOffset ← evalExpr fields state offset
      some (state.world.transientStorage resolvedOffset).val
  | .calldataload offset => do
      let resolvedOffset ← evalExpr fields state offset
      some (Compiler.Proofs.YulGeneration.calldataloadWord state.selector state.world.calldata resolvedOffset)
  | .extcodesize addr => do
      let resolvedAddr ← evalExpr fields state addr
      some (state.world.codeSize (resolvedAddr % addressModulus)).val
  | .returndataOptionalBoolAt offset => do
      let resolvedOffset ← evalExpr fields state offset
      some (state.world.returndataOptionalBool resolvedOffset)
  -- The reserved `exp` builtin lane. `pow`/`^` in the EDSL surfaces as
  -- `externalCall builtinExpName [base, exponent]`, but it carries no foreign
  -- behaviour: the compiler lowers it to the pure Yul `exp` builtin.
  | .externalCall name [base, exponent] =>
      if name == builtinExpName then do
        let baseVal ← evalExpr fields state base
        let exponentVal ← evalExpr fields state exponent
        pure (Verity.Core.Uint256.powEff
          (Verity.Core.Uint256.ofNat baseVal)
          (Verity.Core.Uint256.ofNat exponentVal)).val
      else none
  | .keccak256 offExpr sizeExpr => do
      let off ← evalExpr fields state offExpr
      let size ← evalExpr fields state sizeExpr
      some (keccakMemorySlice state.world.memory off size)
  | .constructorArg idx =>
      lookupBinding? state.bindings s!"arg{idx}"
  | .arrayElementDynamicWord name index wordOffset => do
      let idx ← evalExpr fields state index
      let (dataOffset, length) ← dynamicArrayBinding? state.bindings name
      arrayElementDynamicWord?
        state.selector state.world.calldata dataOffset length idx wordOffset
  | _ => none

def evalExprList (fields : List Field) (state : RuntimeState) : List Expr → Option (List Nat)
  | [] => some []
  | expr :: rest => do
      let value ← evalExpr fields state expr
      let values ← evalExprList fields state rest
      pure (value :: values)

private theorem evalExpr_literal
    (fields : List Field)
    (state : RuntimeState)
    (n : Nat) :
    evalExpr fields state (.literal n) = some (wordNormalize n) := rfl

private theorem evalExpr_param
    (fields : List Field)
    (state : RuntimeState)
    (name : String) :
    evalExpr fields state (.param name) = some (lookupValue state.bindings name) := rfl

private theorem evalExpr_immutable
    (fields : List Field)
    (state : RuntimeState)
    (name : String) :
    evalExpr fields state (.immutable name) = some (state.immutable name).val := rfl

private theorem evalExpr_localVar
    (fields : List Field)
    (state : RuntimeState)
    (name : String) :
    evalExpr fields state (.localVar name) = some (lookupValue state.bindings name) := rfl

private theorem evalExpr_caller
    (fields : List Field)
    (state : RuntimeState) :
    evalExpr fields state .caller = some state.world.sender.val := rfl

private theorem evalExpr_contractAddress
    (fields : List Field)
    (state : RuntimeState) :
    evalExpr fields state .contractAddress = some state.world.thisAddress.val := rfl

private theorem evalExpr_chainid
    (fields : List Field)
    (state : RuntimeState) :
    evalExpr fields state .chainid = some state.world.chainId.val := rfl

private theorem evalExpr_txOrigin
    (fields : List Field)
    (state : RuntimeState) :
    evalExpr fields state .txOrigin = some state.world.txOrigin.val := rfl

private theorem evalExpr_msgValue
    (fields : List Field)
    (state : RuntimeState) :
    evalExpr fields state .msgValue = some state.world.msgValue.val := rfl

private theorem evalExpr_selfBalance
    (fields : List Field)
    (state : RuntimeState) :
    evalExpr fields state .selfBalance = some state.world.selfBalance.val := rfl

private theorem evalExpr_blockTimestamp
    (fields : List Field)
    (state : RuntimeState) :
    evalExpr fields state .blockTimestamp = some state.world.blockTimestamp.val := rfl

private theorem evalExpr_blockNumber
    (fields : List Field)
    (state : RuntimeState) :
    evalExpr fields state .blockNumber = some state.world.blockNumber.val := rfl

private theorem evalExpr_storage
    (fields : List Field)
    (state : RuntimeState)
    (fieldName : String) :
      evalExpr fields state (.storage fieldName) =
        match findFieldWithResolvedSlot fields fieldName with
        | some (field, slot) =>
            let rawWord := (readFieldWord state.world field slot).val
            match field.packedBits with
            | none => some rawWord
            | some packed =>
                some (Verity.Core.Uint256.and
                  (Verity.Core.Uint256.shr packed.offset rawWord)
                  (packedMaskNat packed)).val
        | none => none := rfl

private theorem evalExpr_storageAddr
    (fields : List Field)
    (state : RuntimeState)
    (fieldName : String) :
      evalExpr fields state (.storageAddr fieldName) =
        match findFieldWithResolvedSlot fields fieldName with
        | some (field, slot) =>
            if field.isTransient then
              some (state.world.transientStorage (wordNormalize slot)).val
            else
              some (state.world.storageAddr (wordNormalize slot)).val
        | none => none := rfl

private theorem evalExpr_storageArrayLength
    (fields : List Field)
    (state : RuntimeState)
    (fieldName : String) :
    evalExpr fields state (.storageArrayLength fieldName) =
      match findFieldWithResolvedSlot fields fieldName with
      | some ({ ty := .dynamicArray _, .. }, slot) => some (state.world.storageArray slot).length
      | _ => none := rfl

private theorem evalExpr_constructorArg
    (fields : List Field)
    (state : RuntimeState)
    (idx : Nat) :
    evalExpr fields state (.constructorArg idx) =
      lookupBinding? state.bindings s!"arg{idx}" := rfl

private theorem evalExpr_blobbasefee
    (fields : List Field)
    (state : RuntimeState) :
    evalExpr fields state .blobbasefee = some state.world.blobBaseFee.val := rfl

private theorem evalExpr_calldatasize
    (fields : List Field)
    (state : RuntimeState) :
    evalExpr fields state .calldatasize = some state.world.calldataSize.val := rfl

/-- `returndatasize()` reads the EIP-211 returndata buffer, measured in bytes.
The buffer is empty at frame entry and is replaced wholesale by each call-family
instruction with the callee's return data. -/
private theorem evalExpr_returndataSize
    (fields : List Field)
    (state : RuntimeState) :
    evalExpr fields state .returndataSize
      = some state.world.returndataSize := rfl

private theorem evalExpr_arrayLength
    (fields : List Field)
    (state : RuntimeState)
    (name : String) :
    evalExpr fields state (.arrayLength name) =
      lookupBinding? state.bindings s!"{name}_length" := rfl

private theorem evalExpr_memoryArrayLength
    (fields : List Field)
    (state : RuntimeState)
    (name : String) :
    evalExpr fields state (.memoryArrayLength name) =
      lookupBinding? state.bindings s!"{name}_length" := rfl

private theorem evalExpr_dynamicBytesEq
    (fields : List Field)
    (state : RuntimeState)
    (lhsName rhsName : String) :
    evalExpr fields state (.dynamicBytesEq lhsName rhsName) = (do
      let (lhsOffset, lhsLength) ← dynamicArrayBinding? state.bindings lhsName
      let (rhsOffset, rhsLength) ← dynamicArrayBinding? state.bindings rhsName
      some (boolWord (DynamicAbi.dynamicBytesEqCalldata state.selector state.world.calldata
        lhsOffset lhsLength rhsOffset rhsLength))) := rfl

/-- The reserved `exp` builtin lane is the only `externalCall` shape the source
semantics evaluates; it denotes `Uint256.pow` on the two operand values. -/
theorem evalExpr_externalCall_builtinExp
    (fields : List Field)
    (state : RuntimeState)
    (base exponent : Expr) :
    evalExpr fields state (.externalCall builtinExpName [base, exponent]) = (do
      let baseVal ← evalExpr fields state base
      let exponentVal ← evalExpr fields state exponent
      pure (Verity.Core.Uint256.pow
        (Verity.Core.Uint256.ofNat baseVal)
        (Verity.Core.Uint256.ofNat exponentVal)).val) := by
  simp [evalExpr, Verity.Core.Uint256.powEff_eq_pow]

private theorem evalExpr_externalCall_of_ne
    (fields : List Field)
    (state : RuntimeState)
    (name : String)
    (args : List Expr)
    (hname : name ≠ builtinExpName) :
    evalExpr fields state (.externalCall name args) = none := by
  match args with
  | [] | [_] | _ :: _ :: _ :: _ => rfl
  | [_, _] => simp [evalExpr, hname]

private theorem evalExpr_externalCall_of_arity
    (fields : List Field)
    (state : RuntimeState)
    (name : String)
    (args : List Expr)
    (harity : args.length ≠ 2) :
    evalExpr fields state (.externalCall name args) = none := by
  match args with
  | [] | [_] | _ :: _ :: _ :: _ => rfl
  | [_, _] => simp at harity

private theorem evalExpr_mload
    (fields : List Field)
    (state : RuntimeState)
    (a : Expr) :
    evalExpr fields state (.mload a) =
      (evalExpr fields state a).bind
        (fun offset => some (state.world.memory offset).val) := rfl

private theorem evalExpr_tload
    (fields : List Field)
    (state : RuntimeState)
    (a : Expr) :
    evalExpr fields state (.tload a) =
      (evalExpr fields state a).bind
        (fun resolvedOffset => some (state.world.transientStorage resolvedOffset).val) := rfl

private theorem evalExpr_calldataload
    (fields : List Field)
    (state : RuntimeState)
    (a : Expr) :
    evalExpr fields state (.calldataload a) =
      (evalExpr fields state a).bind
        (fun resolvedOffset => some (Compiler.Proofs.YulGeneration.calldataloadWord state.selector state.world.calldata resolvedOffset)) := rfl

private theorem evalExpr_extcodesize
    (fields : List Field)
    (state : RuntimeState)
    (a : Expr) :
    evalExpr fields state (.extcodesize a) =
      (evalExpr fields state a).bind
        (fun resolvedAddr => some (state.world.codeSize (resolvedAddr % addressModulus)).val) := rfl

private theorem evalExpr_returndataOptionalBoolAt
    (fields : List Field)
    (state : RuntimeState)
    (a : Expr) :
    evalExpr fields state (.returndataOptionalBoolAt a) =
      (evalExpr fields state a).bind
        (fun resolvedOffset => some (state.world.returndataOptionalBool resolvedOffset)) := rfl

private theorem evalExpr_keccak256
    (fields : List Field)
    (state : RuntimeState)
    (a b : Expr) :
    evalExpr fields state (.keccak256 a b) = (do
      let off ← evalExpr fields state a
      let size ← evalExpr fields state b
      some (keccakMemorySlice state.world.memory off size)) := rfl

private theorem evalExpr_mulDiv512Down
    (fields : List Field)
    (state : RuntimeState)
    (a b c : Expr) :
    evalExpr fields state (.mulDiv512Down a b c) = none := rfl

private theorem evalExpr_mulDiv512Up
    (fields : List Field)
    (state : RuntimeState)
    (a b c : Expr) :
    evalExpr fields state (.mulDiv512Up a b c) = none := rfl

private theorem evalExpr_paramDynamicHeadWord
    (fields : List Field)
    (state : RuntimeState)
    (name : String)
    (wordOffset : Nat) :
    evalExpr fields state (.paramDynamicHeadWord name wordOffset) = none := rfl

private theorem evalExpr_paramDynamicStaticComposite
    (fields : List Field)
    (state : RuntimeState)
    (name : String)
    (wordOffset : Nat) :
    evalExpr fields state (.paramDynamicStaticComposite name wordOffset) = none := rfl

private theorem evalExpr_paramDynamicMemberLength
    (fields : List Field)
    (state : RuntimeState)
    (name : String)
    (wordOffset : Nat) :
    evalExpr fields state (.paramDynamicMemberLength name wordOffset) = none := rfl

private theorem evalExpr_paramDynamicMemberDataOffset
    (fields : List Field)
    (state : RuntimeState)
    (name : String)
    (wordOffset : Nat) :
    evalExpr fields state (.paramDynamicMemberDataOffset name wordOffset) = none := rfl

private theorem evalExpr_paramDynamicMemberElement
    (fields : List Field)
    (state : RuntimeState)
    (name : String)
    (wordOffset : Nat)
    (innerIndex : Expr) :
    evalExpr fields state (.paramDynamicMemberElement name wordOffset innerIndex) = none := rfl

private theorem evalExpr_call
    (fields : List Field)
    (state : RuntimeState)
    (g t v io is oo os : Expr) :
    evalExpr fields state (.call g t v io is oo os) = none := rfl

private theorem evalExpr_staticcall
    (fields : List Field)
    (state : RuntimeState)
    (g t io is oo os : Expr) :
    evalExpr fields state (.staticcall g t io is oo os) = none := rfl

private theorem evalExpr_delegatecall
    (fields : List Field)
    (state : RuntimeState)
    (g t io is oo os : Expr) :
    evalExpr fields state (.delegatecall g t io is oo os) = none := rfl

private theorem evalExpr_add
    (fields : List Field)
    (state : RuntimeState)
    (a b : Expr) :
    evalExpr fields state (.add a b) = (do
      let lhs : Verity.Core.Uint256 := ← evalExpr fields state a
      let rhs : Verity.Core.Uint256 := ← evalExpr fields state b
      pure (lhs + rhs).val) := rfl

private theorem evalExpr_sub
    (fields : List Field)
    (state : RuntimeState)
    (a b : Expr) :
    evalExpr fields state (.sub a b) = (do
      let lhs : Verity.Core.Uint256 := ← evalExpr fields state a
      let rhs : Verity.Core.Uint256 := ← evalExpr fields state b
      pure (lhs - rhs).val) := rfl

private theorem evalExpr_mul
    (fields : List Field)
    (state : RuntimeState)
    (a b : Expr) :
    evalExpr fields state (.mul a b) = (do
      let lhs : Verity.Core.Uint256 := ← evalExpr fields state a
      let rhs : Verity.Core.Uint256 := ← evalExpr fields state b
      pure (lhs * rhs).val) := rfl

private theorem evalExpr_div
    (fields : List Field)
    (state : RuntimeState)
    (a b : Expr) :
    evalExpr fields state (.div a b) = (do
      let lhs : Verity.Core.Uint256 := ← evalExpr fields state a
      let rhs : Verity.Core.Uint256 := ← evalExpr fields state b
      pure (lhs / rhs).val) := rfl

private theorem evalExpr_mod
    (fields : List Field)
    (state : RuntimeState)
    (a b : Expr) :
    evalExpr fields state (.mod a b) = (do
      let lhs : Verity.Core.Uint256 := ← evalExpr fields state a
      let rhs : Verity.Core.Uint256 := ← evalExpr fields state b
      pure (lhs % rhs).val) := rfl

private theorem evalExpr_eq
    (fields : List Field)
    (state : RuntimeState)
    (a b : Expr) :
    evalExpr fields state (.eq a b) = (do
      let lhs ← evalExpr fields state a
      let rhs ← evalExpr fields state b
      pure (boolWord (decide (lhs = rhs)))) := rfl

private theorem evalExpr_ge
    (fields : List Field)
    (state : RuntimeState)
    (a b : Expr) :
    evalExpr fields state (.ge a b) = (do
      let lhs ← evalExpr fields state a
      let rhs ← evalExpr fields state b
      pure (boolWord (decide (rhs ≤ lhs)))) := rfl

private theorem evalExpr_gt
    (fields : List Field)
    (state : RuntimeState)
    (a b : Expr) :
    evalExpr fields state (.gt a b) = (do
      let lhs ← evalExpr fields state a
      let rhs ← evalExpr fields state b
      pure (boolWord (decide (rhs < lhs)))) := rfl

private theorem evalExpr_lt
    (fields : List Field)
    (state : RuntimeState)
    (a b : Expr) :
    evalExpr fields state (.lt a b) = (do
      let lhs ← evalExpr fields state a
      let rhs ← evalExpr fields state b
      pure (boolWord (decide (lhs < rhs)))) := rfl

private theorem evalExpr_le
    (fields : List Field)
    (state : RuntimeState)
    (a b : Expr) :
    evalExpr fields state (.le a b) = (do
      let lhs ← evalExpr fields state a
      let rhs ← evalExpr fields state b
      pure (boolWord (decide (lhs ≤ rhs)))) := rfl

private theorem evalExpr_logicalAnd
    (fields : List Field)
    (state : RuntimeState)
    (a b : Expr) :
    evalExpr fields state (.logicalAnd a b) = (do
      let lhs ← evalExpr fields state a
      let rhs ← evalExpr fields state b
      pure (boolWord (decide (lhs != 0) && decide (rhs != 0)))) := rfl

private theorem evalExpr_logicalOr
    (fields : List Field)
    (state : RuntimeState)
    (a b : Expr) :
    evalExpr fields state (.logicalOr a b) = (do
      let lhs ← evalExpr fields state a
      let rhs ← evalExpr fields state b
      pure (boolWord (decide (lhs != 0) || decide (rhs != 0)))) := rfl

private theorem evalExpr_sdiv
    (fields : List Field)
    (state : RuntimeState)
    (a b : Expr) :
    evalExpr fields state (.sdiv a b) = (do
      let lhs ← evalExpr fields state a
      let rhs ← evalExpr fields state b
      pure (Verity.Core.Int256.div
        (Verity.Core.Int256.ofUint256 (Verity.Core.Uint256.ofNat lhs))
        (Verity.Core.Int256.ofUint256 (Verity.Core.Uint256.ofNat rhs))).toUint256.val) := rfl

private theorem evalExpr_smod
    (fields : List Field)
    (state : RuntimeState)
    (a b : Expr) :
    evalExpr fields state (.smod a b) = (do
      let lhs ← evalExpr fields state a
      let rhs ← evalExpr fields state b
      pure (Verity.Core.Int256.mod
        (Verity.Core.Int256.ofUint256 (Verity.Core.Uint256.ofNat lhs))
        (Verity.Core.Int256.ofUint256 (Verity.Core.Uint256.ofNat rhs))).toUint256.val) := rfl

private theorem evalExpr_sgt
    (fields : List Field)
    (state : RuntimeState)
    (a b : Expr) :
    evalExpr fields state (.sgt a b) = (do
      let lhs ← evalExpr fields state a
      let rhs ← evalExpr fields state b
      pure (boolWord (decide (
        (Verity.Core.Int256.ofUint256 (Verity.Core.Uint256.ofNat rhs) : Int) <
        (Verity.Core.Int256.ofUint256 (Verity.Core.Uint256.ofNat lhs) : Int))))) := rfl

private theorem evalExpr_slt
    (fields : List Field)
    (state : RuntimeState)
    (a b : Expr) :
    evalExpr fields state (.slt a b) = (do
      let lhs ← evalExpr fields state a
      let rhs ← evalExpr fields state b
      pure (boolWord (decide (
        (Verity.Core.Int256.ofUint256 (Verity.Core.Uint256.ofNat lhs) : Int) <
        (Verity.Core.Int256.ofUint256 (Verity.Core.Uint256.ofNat rhs) : Int))))) := rfl

private theorem evalExpr_bitAnd
    (fields : List Field)
    (state : RuntimeState)
    (a b : Expr) :
    evalExpr fields state (.bitAnd a b) = (do
      let lhs ← evalExpr fields state a
      let rhs ← evalExpr fields state b
      pure (Verity.Core.Uint256.and lhs rhs).val) := rfl

private theorem evalExpr_bitOr
    (fields : List Field)
    (state : RuntimeState)
    (a b : Expr) :
    evalExpr fields state (.bitOr a b) = (do
      let lhs ← evalExpr fields state a
      let rhs ← evalExpr fields state b
      pure (Verity.Core.Uint256.or lhs rhs).val) := rfl

private theorem evalExpr_bitXor
    (fields : List Field)
    (state : RuntimeState)
    (a b : Expr) :
    evalExpr fields state (.bitXor a b) = (do
      let lhs ← evalExpr fields state a
      let rhs ← evalExpr fields state b
      pure (Verity.Core.Uint256.xor lhs rhs).val) := rfl

private theorem evalExpr_bitNot
    (fields : List Field)
    (state : RuntimeState)
    (a : Expr) :
    evalExpr fields state (.bitNot a) = (do
      let value ← evalExpr fields state a
      pure (Verity.Core.Uint256.not value).val) := rfl

private theorem evalExpr_shl
    (fields : List Field)
    (state : RuntimeState)
    (shift value : Expr) :
    evalExpr fields state (.shl shift value) = (do
      let shiftVal ← evalExpr fields state shift
      let wordVal ← evalExpr fields state value
      pure (Verity.Core.Uint256.shl shiftVal wordVal).val) := rfl

private theorem evalExpr_shr
    (fields : List Field)
    (state : RuntimeState)
    (shift value : Expr) :
    evalExpr fields state (.shr shift value) = (do
      let shiftVal ← evalExpr fields state shift
      let wordVal ← evalExpr fields state value
      pure (Verity.Core.Uint256.shr shiftVal wordVal).val) := rfl

private theorem evalExpr_sar
    (fields : List Field)
    (state : RuntimeState)
    (shift value : Expr) :
    evalExpr fields state (.sar shift value) = (do
      let lhs ← evalExpr fields state shift
      let rhs ← evalExpr fields state value
      pure (Verity.Core.Int256.sar
        (Verity.Core.Int256.ofUint256 (Verity.Core.Uint256.ofNat lhs))
        (Verity.Core.Int256.ofUint256 (Verity.Core.Uint256.ofNat rhs))).toUint256.val) := rfl

private theorem evalExpr_byte
    (fields : List Field)
    (state : RuntimeState)
    (index value : Expr) :
    evalExpr fields state (.byte index value) = (do
      let i ← evalExpr fields state index
      let v ← evalExpr fields state value
      pure (Verity.Core.Uint256.byte
        (Verity.Core.Uint256.ofNat i)
        (Verity.Core.Uint256.ofNat v)).val) := rfl

private theorem evalExpr_signextend
    (fields : List Field)
    (state : RuntimeState)
    (byteIndex value : Expr) :
    evalExpr fields state (.signextend byteIndex value) = (do
      let b ← evalExpr fields state byteIndex
      let v ← evalExpr fields state value
      pure (Verity.Core.Uint256.signextend
        (Verity.Core.Uint256.ofNat b)
        (Verity.Core.Uint256.ofNat v)).val) := rfl

private theorem evalExpr_logicalNot
    (fields : List Field)
    (state : RuntimeState)
    (a : Expr) :
    evalExpr fields state (.logicalNot a) = (do
      let value ← evalExpr fields state a
      pure (boolWord (decide (value = 0)))) := rfl

private theorem evalExpr_min
    (fields : List Field)
    (state : RuntimeState)
    (a b : Expr) :
    evalExpr fields state (.min a b) = (do
      let lhs ← evalExpr fields state a
      let rhs ← evalExpr fields state b
      pure (if lhs ≤ rhs then lhs else rhs)) := rfl

private theorem evalExpr_max
    (fields : List Field)
    (state : RuntimeState)
    (a b : Expr) :
    evalExpr fields state (.max a b) = (do
      let lhs ← evalExpr fields state a
      let rhs ← evalExpr fields state b
      pure (if rhs ≤ lhs then lhs else rhs)) := rfl

private theorem evalExpr_wMulDown
    (fields : List Field)
    (state : RuntimeState)
    (a b : Expr) :
    evalExpr fields state (.wMulDown a b) = (do
      let lhs : Verity.Core.Uint256 := ← evalExpr fields state a
      let rhs : Verity.Core.Uint256 := ← evalExpr fields state b
      let wad : Verity.Core.Uint256 := 1000000000000000000
      pure ((lhs * rhs) / wad).val) := rfl

private theorem evalExpr_wDivUp
    (fields : List Field)
    (state : RuntimeState)
    (a b : Expr) :
    evalExpr fields state (.wDivUp a b) = (do
      let lhs : Verity.Core.Uint256 := ← evalExpr fields state a
      let rhs : Verity.Core.Uint256 := ← evalExpr fields state b
      let wad : Verity.Core.Uint256 := 1000000000000000000
      pure (((lhs * wad) + (rhs - 1)) / rhs).val) := rfl

private theorem evalExpr_mapping
    (fields : List Field)
    (state : RuntimeState)
    (field : String)
    (key : Expr) :
    evalExpr fields state (.mapping field key) = (do
      let keyVal ← evalExpr fields state key
      match findFieldWithResolvedSlot fields field with
      | some (field, slot) =>
          some (readFieldWord state.world field (Compiler.Proofs.abstractMappingSlot slot keyVal)).val
      | none => none) := rfl

private theorem evalExpr_mappingUint
    (fields : List Field)
    (state : RuntimeState)
    (field : String)
    (key : Expr) :
    evalExpr fields state (.mappingUint field key) = (do
      let keyVal ← evalExpr fields state key
      match findFieldWithResolvedSlot fields field with
      | some (field, slot) =>
          some (readFieldWord state.world field (Compiler.Proofs.abstractMappingSlot slot keyVal)).val
      | none => none) := rfl

private theorem evalExpr_arrayElement
    (fields : List Field)
    (state : RuntimeState)
    (name : String)
    (index : Expr) :
    evalExpr fields state (.arrayElement name index) = (do
      let idx ← evalExpr fields state index
      let (dataOffset, length) ← dynamicArrayBinding? state.bindings name
      arrayElement? state.selector state.world.calldata dataOffset length idx) := rfl

private theorem evalExpr_memoryArrayElement
    (fields : List Field)
    (state : RuntimeState)
    (name : String)
    (index : Expr) :
    evalExpr fields state (.memoryArrayElement name index) =
      (do let idx ← evalExpr fields state index
          let (dataOffset, length) ← dynamicArrayBinding? state.bindings name
          if idx < length then
            some (state.world.memory (wordNormalize (dataOffset + 32 * idx))).val
          else
            none) := rfl

private theorem evalExpr_arrayElementWord
    (fields : List Field)
    (state : RuntimeState)
    (name : String)
    (index : Expr)
    (elementWords wordOffset : Nat) :
    evalExpr fields state (.arrayElementWord name index elementWords wordOffset) = none := rfl

private theorem evalExpr_arrayElementDynamicWord
    (fields : List Field)
    (state : RuntimeState)
    (name : String)
    (index : Expr)
    (wordOffset : Nat) :
    evalExpr fields state (.arrayElementDynamicWord name index wordOffset) = (do
      let idx ← evalExpr fields state index
      let (dataOffset, length) ← dynamicArrayBinding? state.bindings name
      arrayElementDynamicWord?
        state.selector state.world.calldata dataOffset length idx wordOffset) := rfl

private theorem evalExpr_arrayElementDynamicDataOffset
    (fields : List Field)
    (state : RuntimeState)
    (name : String)
    (index : Expr) :
    evalExpr fields state (.arrayElementDynamicDataOffset name index) = (do
      let idx ← evalExpr fields state index
      let (dataOffset, length) ← dynamicArrayBinding? state.bindings name
      arrayElementDynamicHeadOffset?
        state.selector state.world.calldata dataOffset length idx) := rfl

private theorem evalExpr_arrayElementDynamicMemberLength
    (fields : List Field)
    (state : RuntimeState)
    (name : String)
    (index : Expr)
    (wordOffset : Nat) :
    evalExpr fields state (.arrayElementDynamicMemberLength name index wordOffset) = (do
      let idx ← evalExpr fields state index
      let (dataOffset, length) ← dynamicArrayBinding? state.bindings name
      arrayElementDynamicMemberLength?
        state.selector state.world.calldata dataOffset length idx wordOffset) := rfl

private theorem evalExpr_arrayElementDynamicMemberDataOffset
    (fields : List Field)
    (state : RuntimeState)
    (name : String)
    (index : Expr)
    (wordOffset : Nat) :
    evalExpr fields state (.arrayElementDynamicMemberDataOffset name index wordOffset) = (do
      let idx ← evalExpr fields state index
      let (dataOffset, length) ← dynamicArrayBinding? state.bindings name
      arrayElementDynamicMemberDataOffset?
        state.selector state.world.calldata dataOffset length idx wordOffset) := rfl

private theorem evalExpr_arrayElementDynamicMemberElement
    (fields : List Field)
    (state : RuntimeState)
    (name : String)
    (index : Expr)
    (wordOffset : Nat)
    (innerIndex : Expr) :
    evalExpr fields state
        (.arrayElementDynamicMemberElement name index wordOffset innerIndex) = (do
      let idx ← evalExpr fields state index
      let innerIdx ← evalExpr fields state innerIndex
      let (dataOffset, length) ← dynamicArrayBinding? state.bindings name
      arrayElementDynamicMemberElement?
        state.selector state.world.calldata dataOffset length idx wordOffset innerIdx) := rfl

private theorem evalExpr_mappingWord
    (fields : List Field)
    (state : RuntimeState)
    (field : String)
    (key : Expr)
    (wordOffset : Nat) :
    evalExpr fields state (.mappingWord field key wordOffset) = (do
      let keyVal ← evalExpr fields state key
      match findFieldWithResolvedSlot fields field with
      | some (field, slot) =>
          some (readFieldWord state.world field
            (wordNormalize (Compiler.Proofs.abstractMappingSlot slot keyVal + wordOffset))).val
      | none => none) := rfl

private theorem evalExpr_mappingPackedWord
    (fields : List Field)
    (state : RuntimeState)
    (field : String)
    (key : Expr)
    (wordOffset : Nat)
    (packed : PackedBits) :
    evalExpr fields state (.mappingPackedWord field key wordOffset packed) = (do
      let keyVal ← evalExpr fields state key
      match findFieldWithResolvedSlot fields field with
      | some (fieldInfo, slot) =>
          let targetSlot := wordNormalize
            (Compiler.Proofs.abstractMappingSlot slot keyVal + wordOffset)
          let rawWord := (readFieldWord state.world fieldInfo targetSlot).val
          some (Verity.Core.Uint256.and
            (Verity.Core.Uint256.shr packed.offset rawWord)
            (packedMaskNat packed)).val
      | none => none) := rfl

private theorem evalExpr_structMember
    (fields : List Field)
    (state : RuntimeState)
    (field : String)
    (key : Expr)
    (memberName : String) :
    evalExpr fields state (.structMember field key memberName) = (do
      let keyVal ← evalExpr fields state key
      match findFieldWithResolvedSlot fields field, findStructMembers fields field with
      | some (fieldInfo, slot), some members =>
          match findStructMember members memberName with
          | some member =>
              let targetSlot := wordNormalize
                (Compiler.Proofs.abstractMappingSlot slot keyVal + member.wordOffset)
              let rawWord := (readFieldWord state.world fieldInfo targetSlot).val
              match member.packed with
              | none => some rawWord
              | some packed =>
                  some (Verity.Core.Uint256.and
                    (Verity.Core.Uint256.shr packed.offset rawWord)
                    (packedMaskNat packed)).val
          | none => none
      | _, _ => none) := rfl

private theorem evalExpr_storageArrayElement
    (fields : List Field)
    (state : RuntimeState)
    (fieldName : String)
    (index : Expr) :
    evalExpr fields state (.storageArrayElement fieldName index) = (do
      let idx ← evalExpr fields state index
      match findFieldWithResolvedSlot fields fieldName with
      | some ({ ty := .dynamicArray _, .. }, slot) =>
          match (state.world.storageArray slot)[idx]? with
          | some value => some value.val
          | none => none
      | some ({ ty := .fixedArrayUint128 size, .. }, slot) =>
          readFixedUint128ArrayElement state.world slot size idx
      | _ => none) := rfl

private theorem evalExpr_mapping2
    (fields : List Field)
    (state : RuntimeState)
    (field : String)
    (key1 key2 : Expr) :
    evalExpr fields state (.mapping2 field key1 key2) = (do
      let key1Val ← evalExpr fields state key1
      let key2Val ← evalExpr fields state key2
      match findFieldWithResolvedSlot fields field with
      | some (field, slot) =>
          let innerSlot := Compiler.Proofs.abstractMappingSlot slot key1Val
          some (readFieldWord state.world field (Compiler.Proofs.abstractMappingSlot innerSlot key2Val)).val
      | none => none) := rfl

private theorem evalExpr_mappingChain_singleton
    (fields : List Field)
    (state : RuntimeState)
    (field : String)
    (key : Expr) :
    evalExpr fields state (.mappingChain field [key]) = (do
      let keyVal ← evalExpr fields state key
      match findFieldWithResolvedSlot fields field with
      | some (field, slot) =>
          some (readFieldWord state.world field (Compiler.Proofs.abstractMappingSlot slot keyVal)).val
      | none => none) := rfl

private theorem evalExpr_mappingChain_pair
    (fields : List Field)
    (state : RuntimeState)
    (field : String)
    (key1 key2 : Expr) :
    evalExpr fields state (.mappingChain field [key1, key2]) = (do
      let key1Val ← evalExpr fields state key1
      let key2Val ← evalExpr fields state key2
      match findFieldWithResolvedSlot fields field with
      | some (field, slot) =>
          let innerSlot := Compiler.Proofs.abstractMappingSlot slot key1Val
          some (readFieldWord state.world field (Compiler.Proofs.abstractMappingSlot innerSlot key2Val)).val
      | none => none) := rfl

private theorem evalExpr_mapping2Word
    (fields : List Field)
    (state : RuntimeState)
    (field : String)
    (key1 key2 : Expr)
    (wordOffset : Nat) :
    evalExpr fields state (.mapping2Word field key1 key2 wordOffset) = (do
      let key1Val ← evalExpr fields state key1
      let key2Val ← evalExpr fields state key2
      match findFieldWithResolvedSlot fields field with
      | some (field, slot) =>
          let innerSlot := Compiler.Proofs.abstractMappingSlot slot key1Val
          let outerSlot := Compiler.Proofs.abstractMappingSlot innerSlot key2Val
          some (readFieldWord state.world field (wordNormalize (outerSlot + wordOffset))).val
      | none => none) := rfl

private theorem evalExpr_structMember2
    (fields : List Field)
    (state : RuntimeState)
    (field : String)
    (key1 key2 : Expr)
    (memberName : String) :
    evalExpr fields state (.structMember2 field key1 key2 memberName) = (do
      let key1Val ← evalExpr fields state key1
      let key2Val ← evalExpr fields state key2
      match findFieldWithResolvedSlot fields field, findStructMembers fields field with
      | some (fieldInfo, slot), some members =>
          match findStructMember members memberName with
          | some member =>
              let innerSlot := Compiler.Proofs.abstractMappingSlot slot key1Val
              let outerSlot := Compiler.Proofs.abstractMappingSlot innerSlot key2Val
              let targetSlot := wordNormalize (outerSlot + member.wordOffset)
              let rawWord := (readFieldWord state.world fieldInfo targetSlot).val
              match member.packed with
              | none => some rawWord
              | some packed =>
                  some (Verity.Core.Uint256.and
                    (Verity.Core.Uint256.shr packed.offset rawWord)
                    (packedMaskNat packed)).val
          | none => none
      | _, _ => none) := rfl

private theorem evalExpr_ceilDiv
    (fields : List Field)
    (state : RuntimeState)
    (a b : Expr) :
    evalExpr fields state (.ceilDiv a b) = (do
      let lhs : Verity.Core.Uint256 := ← evalExpr fields state a
      let rhs : Verity.Core.Uint256 := ← evalExpr fields state b
      pure (ceilDivVal lhs rhs)) := rfl

private theorem evalExpr_mulDivDown
    (fields : List Field)
    (state : RuntimeState)
    (a b c : Expr) :
    evalExpr fields state (.mulDivDown a b c) = (do
      let lhs : Verity.Core.Uint256 := ← evalExpr fields state a
      let rhs : Verity.Core.Uint256 := ← evalExpr fields state b
      let denom : Verity.Core.Uint256 := ← evalExpr fields state c
      pure ((lhs * rhs) / denom).val) := rfl

private theorem evalExpr_mulDivUp
    (fields : List Field)
    (state : RuntimeState)
    (a b c : Expr) :
    evalExpr fields state (.mulDivUp a b c) = (do
      let lhs : Verity.Core.Uint256 := ← evalExpr fields state a
      let rhs : Verity.Core.Uint256 := ← evalExpr fields state b
      let denom : Verity.Core.Uint256 := ← evalExpr fields state c
      pure (((lhs * rhs) + (denom - 1)) / denom).val) := rfl

private theorem evalExpr_ite
    (fields : List Field)
    (state : RuntimeState)
    (cond thenVal elseVal : Expr) :
    evalExpr fields state (.ite cond thenVal elseVal) = (do
      let condVal ← evalExpr fields state cond
      if condVal != 0 then
        evalExpr fields state thenVal
      else
        evalExpr fields state elseVal) := rfl

private theorem evalExpr_forkIfAtLeast
    (fields : List Field)
    (state : RuntimeState)
    (required : Verity.Core.Intrinsics.HardFork)
    (thenExpr elseExpr : Expr) :
    evalExpr fields state (.forkIfAtLeast required thenExpr elseExpr) = none := rfl

/-- Source-level custom-error revert at the current observable granularity.

`StmtResult` does not yet carry returndata, so the ABI selector and encoded
typed payload produced by compiled Yul are intentionally not observable here.
That richer payload relation is deferred to the planned `StmtResult`/`IRResult`
returndata extension. The argument list is still evaluated on the reverting
path to match the compiled code's control-flow surface; success for
`requireError` skips argument evaluation. -/
def typedErrorRevertResult (fields : List Field) (state : RuntimeState) (args : List Expr) :
    StmtResult :=
  match evalExprList fields state args with
  | _ => .revert

mutual
  def execStmtWithEvents (fields : List Field) (events : List EventDef) :
      RuntimeState → Stmt → StmtResult
    | state, .letVar name value =>
        match evalExpr fields state value with
        | some resolved =>
            .continue { state with bindings := bindValue state.bindings name resolved }
        | none => .revert
    | state, .assignVar name value =>
        match evalExpr fields state value with
        | some resolved =>
            .continue { state with bindings := bindValue state.bindings name resolved }
        | none => .revert
    | state, .setStorage fieldName value =>
        match findFieldWriteSlots fields fieldName, evalExpr fields state value with
        | some slots, some resolved =>
            .continue { state with world := writeUintFieldSlots fields fieldName state.world slots resolved }
        | _, _ => .revert
    | state, .setStorageWord fieldName wordOffset value =>
        match findFieldWriteSlots fields fieldName, evalExpr fields state value with
        | some slots, some resolved =>
            .continue
              { state with
                  world := writeStorageWordFieldSlots fields fieldName state.world slots wordOffset resolved }
        | _, _ => .revert
    | state, .setMapping fieldName key value =>
        match findFieldWriteSlots fields fieldName,
            evalExpr fields state key,
            evalExpr fields state value with
        | some slots@(_ :: _), some resolvedKey, some resolved =>
            .continue
              { state with
                  world := writeAddressKeyedMappingFieldSlots
                    fields fieldName state.world slots resolvedKey resolved }
        | _, _, _ => .revert
    | state, .setMappingWord fieldName key wordOffset value =>
        match findFieldWriteSlots fields fieldName,
            evalExpr fields state key,
            evalExpr fields state value with
        | some slots@(_ :: _), some resolvedKey, some resolved =>
            .continue
               { state with
                   world := writeAddressKeyedMappingWordFieldSlots
                     fields fieldName state.world slots resolvedKey wordOffset resolved }
        | _, _, _ => .revert
    | state, .setMappingPackedWord fieldName key wordOffset packed value =>
        match findFieldWriteSlots fields fieldName,
            evalExpr fields state key,
            evalExpr fields state value with
        | some slots@(_ :: _), some resolvedKey, some resolved =>
            if packedBitsValid packed then
              .continue
                { state with
                    world := writeAddressKeyedMappingPackedWordFieldSlots
                      fields fieldName state.world slots resolvedKey wordOffset packed resolved }
            else
              .revert
        | _, _, _ => .revert
    | state, .setStructMember fieldName key memberName value =>
        match findFieldWriteSlots fields fieldName,
            findStructMembers fields fieldName,
            evalExpr fields state key,
            evalExpr fields state value with
        | some slots@(_ :: _), some members, some resolvedKey, some resolved =>
            match findStructMember members memberName with
            | some { wordOffset := wordOffset, packed := none, .. } =>
                .continue
                  { state with
                      world := writeAddressKeyedMappingWordFieldSlots
                        fields fieldName state.world slots resolvedKey wordOffset resolved }
            | some { wordOffset := wordOffset, packed := some packed, .. } =>
                if packedBitsValid packed then
                  .continue
                    { state with
                        world := writeAddressKeyedMappingPackedWordFieldSlots
                          fields fieldName state.world slots resolvedKey wordOffset packed resolved }
                else
                  .revert
            | _ => .revert
        | _, _, _, _ => .revert
    | state, .setMapping2 fieldName key1 key2 value =>
        match findFieldWriteSlots fields fieldName,
            evalExpr fields state key1,
            evalExpr fields state key2,
            evalExpr fields state value with
        | some slots@(_ :: _), some resolvedKey1, some resolvedKey2, some resolved =>
            .continue
              { state with
                  world :=
                    writeAddressKeyedMapping2FieldSlots
                      fields fieldName state.world slots resolvedKey1 resolvedKey2 resolved }
        | _, _, _, _ => .revert
    | state, .setMapping2Word fieldName key1 key2 wordOffset value =>
        match findFieldWriteSlots fields fieldName,
            evalExpr fields state key1,
            evalExpr fields state key2,
            evalExpr fields state value with
        | some slots@(_ :: _), some resolvedKey1, some resolvedKey2, some resolved =>
            .continue
              { state with
                  world :=
                    writeAddressKeyedMapping2WordFieldSlots
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
            evalExpr fields state key1,
            evalExpr fields state key2,
            evalExpr fields state value with
        | some slots@(_ :: _), some members, some resolvedKey1, some resolvedKey2, some resolved =>
            match findStructMember members memberName with
            | some { wordOffset := wordOffset, packed := none, .. } =>
                .continue
                  { state with
                      world := writeAddressKeyedMapping2WordFieldSlots
                        fields fieldName state.world slots resolvedKey1 resolvedKey2 wordOffset resolved }
            | some { wordOffset := wordOffset, packed := some packed, .. } =>
                if packedBitsValid packed then
                  .continue
                    { state with
                        world := writeAddressKeyedMapping2PackedWordFieldSlots
                          fields fieldName state.world slots resolvedKey1 resolvedKey2 wordOffset packed resolved }
                else
                  .revert
            | _ => .revert
        | _, _, _, _, _ => .revert
    | state, .setMappingUint fieldName key value =>
        match findFieldWriteSlots fields fieldName,
            evalExpr fields state key,
            evalExpr fields state value with
        | some slots@(_ :: _), some resolvedKey, some resolved =>
            .continue
              { state with
                  world := writeUintKeyedMappingFieldSlots
                    fields fieldName state.world slots resolvedKey resolved }
        | _, _, _ => .revert
    | state, .setMappingChain fieldName keys value =>
        match findFieldWriteSlots fields fieldName,
            evalExprList fields state keys,
            evalExpr fields state value with
        | some slots@(_ :: _), some resolvedKeys, some resolved =>
            .continue
              { state with
                  world := writeAddressKeyedMappingChainFieldSlots
                    fields fieldName state.world slots resolvedKeys resolved }
        | _, _, _ => .revert
    | state, .storageArrayPush fieldName value =>
        match findFieldWithResolvedSlot fields fieldName, evalExpr fields state value with
        | some ({ ty := .dynamicArray _, .. }, slot), some resolved =>
            let updated := state.world.storageArray slot ++ [(resolved : Verity.Core.Uint256)]
            .continue { state with world := writeStorageArray state.world slot updated }
        | _, _ => .revert
    | state, .storageArrayPop fieldName =>
        match findFieldWithResolvedSlot fields fieldName with
        | some ({ ty := .dynamicArray _, .. }, slot) =>
            match storageArrayDropLast? (state.world.storageArray slot) with
            | some updated =>
                .continue { state with world := writeStorageArray state.world slot updated }
            | none => .revert
        | _ => .revert
    | state, .setStorageArrayElement fieldName index value =>
        match findFieldWithResolvedSlot fields fieldName, evalExpr fields state index, evalExpr fields state value with
        | some ({ ty := .dynamicArray _, .. }, slot), some idx, some resolved =>
            match storageArraySetAt (state.world.storageArray slot) idx resolved with
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
        match findFieldWriteSlots fields fieldName, evalExpr fields state value with
        | some slots, some resolved =>
            .continue { state with world := writeAddressFieldSlots fields fieldName state.world slots resolved }
        | _, _ => .revert
    | state, .setImmutable name value =>
        match evalExpr fields state value with
        | some resolved =>
            .continue
              { state with
                  immutable := fun immName =>
                    if immName == name then resolved else state.immutable immName }
        | none => .revert
    | state, .mstore offset value =>
        match evalExpr fields state offset, evalExpr fields state value with
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
        match evalExpr fields state offset, evalExpr fields state value with
        | some resolvedOffset, some resolvedValue =>
            let resolvedOffset := wordNormalize resolvedOffset
            .continue {
              state with
              world := state.world.writeTransient resolvedOffset resolvedValue
            }
        | _, _ => .revert
    | state, .calldatacopy destOffset sourceOffset size =>
        match evalExpr fields state destOffset, evalExpr fields state sourceOffset,
            evalExpr fields state size with
        | some dst, some src, some sz =>
            .continue {
              state with
              world := {
                state.world with
                memory := fun o =>
                  if Compiler.Proofs.YulGeneration.calldatacopyWritesAt dst sz o then
                    Verity.Core.Uint256.ofNat
                      (Compiler.Proofs.YulGeneration.calldataloadWord
                        state.selector state.world.calldata (src + (o - dst)))
                  else state.world.memory o
              }
            }
        | _, _, _ => .revert
    | state, .returndataCopy destOffset sourceOffset size =>
        match evalExpr fields state destOffset, evalExpr fields state sourceOffset,
            evalExpr fields state size with
        | some _, some src, some sz =>
            -- RETURNDATACOPY exceptionally halts when `src + size` exceeds the
            -- EIP-211 buffer. Rather than model the partial copy, only the
            -- zero-extent copy is admitted -- it leaves memory untouched whatever
            -- the buffer holds -- and every other extent is conservatively
            -- observed as a failed frame. The IR interpreter branches the same
            -- way, so the two layers agree on the nose.
            if src + sz = 0 then .continue state else .revert
        | _, _, _ => .revert
    | state, .require cond _ =>
        match evalExpr fields state cond with
        | some resolved =>
            if resolved != 0 then .continue state else .revert
        | none => .revert
    | state, .requireError cond _ args =>
        match evalExpr fields state cond with
        | some resolved =>
            if resolved != 0 then .continue state else typedErrorRevertResult fields state args
        | none => .revert
    | state, .revertError _ args =>
        typedErrorRevertResult fields state args
    | state, .return value =>
        match evalExpr fields state value with
        | some resolved => .return resolved
            { state with
                world := { state.world with
                  memory := fun o => if o = 0 then resolved else state.world.memory o } }
        | none => .revert
    | state, .stop => .stop state
    | state, .ite cond thenBranch elseBranch =>
        match evalExpr fields state cond with
        | some resolved =>
            if resolved != 0 then
              execStmtListWithEvents fields events state thenBranch
            else
              execStmtListWithEvents fields events state elseBranch
        | none => .revert
    | state, .emit eventName args =>
        match evalExprList fields state args with
        | some resolved =>
            match eventFromResolvedArgs? events eventName resolved,
                eventScratchMemoryAfterEmit? events eventName resolved state.world.memory with
            | some event, some memory =>
                .continue { state with
                  world := {
                    state.world with
                    memory := memory
                    events := state.world.events ++ [event] } }
            | _, _ => .revert
        | none => .revert
    | state, .forEach varName count body =>
        match evalExpr fields state count with
        | some bound =>
            let initialLoopState :=
              { state with bindings := bindValue state.bindings varName (wordNormalize 0) }
            execForEachLoop varName
              (fun loopState => execStmtListWithEvents fields events loopState body)
              initialLoopState 0 bound
        | none => .revert
    | state, .forEachSetBit varName bitmap body =>
        match evalExpr fields state bitmap with
        | some bits =>
            execForEachSetBitLoop varName
              (fun loopState => execStmtListWithEvents fields events loopState body)
              256 state bits
        | none => .revert
    | _, .revertReturndata => .revert
    | state, .externalCallBind resultVars _externalName args =>
        match evalExprList fields state args with
        | some _ =>
            let outcome := state.externalCallOracle state.externalCallIndex
            if outcome.succeeded then
              if outcome.returnValues.length != resultVars.length then .revert
              else
                .continue
                  { state with
                      world := returndataAfterCall outcome
                        (outcome.postCallWorld.getD state.world)
                      bindings := bindValues state.bindings resultVars
                        (outcome.returnValues.map wordNormalize)
                      externalCallIndex := state.externalCallIndex + 1 }
            else .revert
        | none => .revert
    | state, .tryExternalCallBind successVar resultVars _externalName args =>
        match evalExprList fields state args with
        | some _ =>
            let outcome := state.externalCallOracle state.externalCallIndex
            if outcome.succeeded then
              if outcome.returnValues.length != resultVars.length then .revert
              else
                .continue
                  { state with
                      world := returndataAfterCall outcome
                        (outcome.postCallWorld.getD state.world)
                      bindings := bindValues
                        (bindValue state.bindings successVar 1)
                        resultVars (outcome.returnValues.map wordNormalize)
                      externalCallIndex := state.externalCallIndex + 1 }
            else
              .continue
                { state with
                    world := returndataAfterCall outcome state.world
                    bindings := bindValues
                      (bindValue state.bindings successVar 0)
                      resultVars (outcome.returnValues.map wordNormalize)
                    externalCallIndex := state.externalCallIndex + 1 }
        | none => .revert
    | state, .ecm mod args =>
        match evalExprList fields state args with
        | some _ =>
            let outcome := state.externalCallOracle state.externalCallIndex
            if outcome.succeeded then
              if outcome.returnValues.length != mod.resultVars.length then .revert
              else
                .continue
                  { state with
                      world := returndataAfterCall outcome
                        (mod.committedWorld outcome.postCallWorld state.world)
                      bindings := bindValues state.bindings mod.resultVars
                        (outcome.returnValues.map wordNormalize)
                      externalCallIndex := state.externalCallIndex + 1 }
            else .revert
        | none => .revert
    | _, _ => .revert

  def execStmtListWithEvents (fields : List Field) (events : List EventDef) :
      RuntimeState → List Stmt → StmtResult
    | state, [] => .continue state
    | state, stmt :: rest =>
        match execStmtWithEvents fields events state stmt with
        | .continue next => execStmtListWithEvents fields events next rest
        | .stop next => .stop next
        | .return value next => .return value next
        | .revert => .revert
end

mutual
  def execStmt (fields : List Field) : RuntimeState → Stmt → StmtResult
    | state, .letVar name value =>
        match evalExpr fields state value with
        | some resolved =>
            .continue { state with bindings := bindValue state.bindings name resolved }
        | none => .revert
    | state, .assignVar name value =>
        match evalExpr fields state value with
        | some resolved =>
            .continue { state with bindings := bindValue state.bindings name resolved }
        | none => .revert
    | state, .setStorage fieldName value =>
        match findFieldWriteSlots fields fieldName, evalExpr fields state value with
        | some slots, some resolved =>
            .continue { state with world := writeUintFieldSlots fields fieldName state.world slots resolved }
        | _, _ => .revert
    | state, .setStorageWord fieldName wordOffset value =>
        match findFieldWriteSlots fields fieldName, evalExpr fields state value with
        | some slots, some resolved =>
            .continue
              { state with
                  world := writeStorageWordFieldSlots fields fieldName state.world slots wordOffset resolved }
        | _, _ => .revert
    | state, .setMapping fieldName key value =>
        match findFieldWriteSlots fields fieldName,
            evalExpr fields state key,
            evalExpr fields state value with
        | some slots@(_ :: _), some resolvedKey, some resolved =>
            .continue
              { state with
                  world := writeAddressKeyedMappingFieldSlots
                    fields fieldName state.world slots resolvedKey resolved }
        | _, _, _ => .revert
    | state, .setMappingWord fieldName key wordOffset value =>
        match findFieldWriteSlots fields fieldName,
            evalExpr fields state key,
            evalExpr fields state value with
        | some slots@(_ :: _), some resolvedKey, some resolved =>
            .continue
               { state with
                   world := writeAddressKeyedMappingWordFieldSlots
                     fields fieldName state.world slots resolvedKey wordOffset resolved }
        | _, _, _ => .revert
    | state, .setMappingPackedWord fieldName key wordOffset packed value =>
        match findFieldWriteSlots fields fieldName,
            evalExpr fields state key,
            evalExpr fields state value with
        | some slots@(_ :: _), some resolvedKey, some resolved =>
            if packedBitsValid packed then
              .continue
                { state with
                    world := writeAddressKeyedMappingPackedWordFieldSlots
                      fields fieldName state.world slots resolvedKey wordOffset packed resolved }
            else
              .revert
        | _, _, _ => .revert
    | state, .setStructMember fieldName key memberName value =>
        match findFieldWriteSlots fields fieldName,
            findStructMembers fields fieldName,
            evalExpr fields state key,
            evalExpr fields state value with
        | some slots@(_ :: _), some members, some resolvedKey, some resolved =>
            match findStructMember members memberName with
            | some { wordOffset := wordOffset, packed := none, .. } =>
                .continue
                  { state with
                      world := writeAddressKeyedMappingWordFieldSlots
                        fields fieldName state.world slots resolvedKey wordOffset resolved }
            | some { wordOffset := wordOffset, packed := some packed, .. } =>
                if packedBitsValid packed then
                  .continue
                    { state with
                        world := writeAddressKeyedMappingPackedWordFieldSlots
                          fields fieldName state.world slots resolvedKey wordOffset packed resolved }
                else
                  .revert
            | _ => .revert
        | _, _, _, _ => .revert
    | state, .setMapping2 fieldName key1 key2 value =>
        match findFieldWriteSlots fields fieldName,
            evalExpr fields state key1,
            evalExpr fields state key2,
            evalExpr fields state value with
        | some slots@(_ :: _), some resolvedKey1, some resolvedKey2, some resolved =>
            .continue
              { state with
                  world :=
                    writeAddressKeyedMapping2FieldSlots
                      fields fieldName state.world slots resolvedKey1 resolvedKey2 resolved }
        | _, _, _, _ => .revert
    | state, .setMapping2Word fieldName key1 key2 wordOffset value =>
        match findFieldWriteSlots fields fieldName,
            evalExpr fields state key1,
            evalExpr fields state key2,
            evalExpr fields state value with
        | some slots@(_ :: _), some resolvedKey1, some resolvedKey2, some resolved =>
            .continue
              { state with
                  world :=
                    writeAddressKeyedMapping2WordFieldSlots
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
            evalExpr fields state key1,
            evalExpr fields state key2,
            evalExpr fields state value with
        | some slots@(_ :: _), some members, some resolvedKey1, some resolvedKey2, some resolved =>
            match findStructMember members memberName with
            | some { wordOffset := wordOffset, packed := none, .. } =>
                .continue
                  { state with
                      world := writeAddressKeyedMapping2WordFieldSlots
                        fields fieldName state.world slots resolvedKey1 resolvedKey2 wordOffset resolved }
            | some { wordOffset := wordOffset, packed := some packed, .. } =>
                if packedBitsValid packed then
                  .continue
                    { state with
                        world := writeAddressKeyedMapping2PackedWordFieldSlots
                          fields fieldName state.world slots resolvedKey1 resolvedKey2 wordOffset packed resolved }
                else
                  .revert
            | _ => .revert
        | _, _, _, _, _ => .revert
    | state, .setMappingUint fieldName key value =>
        match findFieldWriteSlots fields fieldName,
            evalExpr fields state key,
            evalExpr fields state value with
        | some slots@(_ :: _), some resolvedKey, some resolved =>
            .continue
              { state with
                  world := writeUintKeyedMappingFieldSlots
                    fields fieldName state.world slots resolvedKey resolved }
        | _, _, _ => .revert
    | state, .setMappingChain fieldName keys value =>
        match findFieldWriteSlots fields fieldName,
            evalExprList fields state keys,
            evalExpr fields state value with
        | some slots@(_ :: _), some resolvedKeys, some resolved =>
            .continue
              { state with
                  world := writeAddressKeyedMappingChainFieldSlots
                    fields fieldName state.world slots resolvedKeys resolved }
        | _, _, _ => .revert
    | state, .storageArrayPush fieldName value =>
        match findFieldWithResolvedSlot fields fieldName, evalExpr fields state value with
        | some ({ ty := .dynamicArray _, .. }, slot), some resolved =>
            let updated := state.world.storageArray slot ++ [(resolved : Verity.Core.Uint256)]
            .continue { state with world := writeStorageArray state.world slot updated }
        | _, _ => .revert
    | state, .storageArrayPop fieldName =>
        match findFieldWithResolvedSlot fields fieldName with
        | some ({ ty := .dynamicArray _, .. }, slot) =>
            match storageArrayDropLast? (state.world.storageArray slot) with
            | some updated =>
                .continue { state with world := writeStorageArray state.world slot updated }
            | none => .revert
        | _ => .revert
    | state, .setStorageArrayElement fieldName index value =>
        match findFieldWithResolvedSlot fields fieldName, evalExpr fields state index, evalExpr fields state value with
        | some ({ ty := .dynamicArray _, .. }, slot), some idx, some resolved =>
            match storageArraySetAt (state.world.storageArray slot) idx resolved with
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
        match findFieldWriteSlots fields fieldName, evalExpr fields state value with
        | some slots, some resolved =>
            .continue { state with world := writeAddressFieldSlots fields fieldName state.world slots resolved }
        | _, _ => .revert
    | state, .setImmutable name value =>
        match evalExpr fields state value with
        | some resolved =>
            .continue
              { state with
                  immutable := fun immName =>
                    if immName == name then resolved else state.immutable immName }
        | none => .revert
    | state, .mstore offset value =>
        match evalExpr fields state offset, evalExpr fields state value with
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
        match evalExpr fields state offset, evalExpr fields state value with
        | some resolvedOffset, some resolvedValue =>
            let resolvedOffset := wordNormalize resolvedOffset
            .continue {
              state with
              world := state.world.writeTransient resolvedOffset resolvedValue
            }
        | _, _ => .revert
    | state, .calldatacopy destOffset sourceOffset size =>
        match evalExpr fields state destOffset, evalExpr fields state sourceOffset,
            evalExpr fields state size with
        | some dst, some src, some sz =>
            .continue {
              state with
              world := {
                state.world with
                memory := fun o =>
                  if Compiler.Proofs.YulGeneration.calldatacopyWritesAt dst sz o then
                    Verity.Core.Uint256.ofNat
                      (Compiler.Proofs.YulGeneration.calldataloadWord
                        state.selector state.world.calldata (src + (o - dst)))
                  else state.world.memory o
              }
            }
        | _, _, _ => .revert
    | state, .returndataCopy destOffset sourceOffset size =>
        match evalExpr fields state destOffset, evalExpr fields state sourceOffset,
            evalExpr fields state size with
        | some _, some src, some sz =>
            -- RETURNDATACOPY exceptionally halts when `src + size` exceeds the
            -- EIP-211 buffer. Rather than model the partial copy, only the
            -- zero-extent copy is admitted -- it leaves memory untouched whatever
            -- the buffer holds -- and every other extent is conservatively
            -- observed as a failed frame. The IR interpreter branches the same
            -- way, so the two layers agree on the nose.
            if src + sz = 0 then .continue state else .revert
        | _, _, _ => .revert
    | state, .require cond _ =>
        match evalExpr fields state cond with
        | some resolved =>
            if resolved != 0 then .continue state else .revert
        | none => .revert
    | state, .requireError cond _ args =>
        match evalExpr fields state cond with
        | some resolved =>
            if resolved != 0 then .continue state else typedErrorRevertResult fields state args
        | none => .revert
    | state, .revertError _ args =>
        typedErrorRevertResult fields state args
    | state, .return value =>
        match evalExpr fields state value with
        | some resolved => .return resolved
            { state with
                world := { state.world with
                  memory := fun o => if o = 0 then resolved else state.world.memory o } }
        | none => .revert
    | state, .stop => .stop state
    | state, .ite cond thenBranch elseBranch =>
        match evalExpr fields state cond with
        | some resolved =>
            if resolved != 0 then
              execStmtList fields state thenBranch
            else
              execStmtList fields state elseBranch
        | none => .revert
    | state, .emit eventName args =>
        match evalExprList fields state args with
        | some resolved =>
            match eventFromResolvedArgs? [] eventName resolved,
                eventScratchMemoryAfterEmit? [] eventName resolved state.world.memory with
            | some event, some memory =>
                .continue { state with
                  world := {
                    state.world with
                    memory := memory
                    events := state.world.events ++ [event] } }
            | _, _ => .revert
        | none => .revert
    | state, .forEach varName count body =>
        match evalExpr fields state count with
        | some bound =>
            let initialLoopState :=
              { state with bindings := bindValue state.bindings varName (wordNormalize 0) }
            execForEachLoop varName
              (fun loopState => execStmtList fields loopState body)
              initialLoopState 0 bound
        | none => .revert
    | state, .forEachSetBit varName bitmap body =>
        match evalExpr fields state bitmap with
        | some bits =>
            execForEachSetBitLoop varName
              (fun loopState => execStmtList fields loopState body)
              256 state bits
        | none => .revert
    | _, .revertReturndata => .revert
    | state, .externalCallBind resultVars _externalName args =>
        match evalExprList fields state args with
        | some _ =>
            let outcome := state.externalCallOracle state.externalCallIndex
            if outcome.succeeded then
              if outcome.returnValues.length != resultVars.length then .revert
              else
                .continue
                  { state with
                      world := returndataAfterCall outcome
                        (outcome.postCallWorld.getD state.world)
                      bindings := bindValues state.bindings resultVars
                        (outcome.returnValues.map wordNormalize)
                      externalCallIndex := state.externalCallIndex + 1 }
            else .revert
        | none => .revert
    | state, .tryExternalCallBind successVar resultVars _externalName args =>
        match evalExprList fields state args with
        | some _ =>
            let outcome := state.externalCallOracle state.externalCallIndex
            if outcome.succeeded then
              if outcome.returnValues.length != resultVars.length then .revert
              else
                .continue
                  { state with
                      world := returndataAfterCall outcome
                        (outcome.postCallWorld.getD state.world)
                      bindings := bindValues
                        (bindValue state.bindings successVar 1)
                        resultVars (outcome.returnValues.map wordNormalize)
                      externalCallIndex := state.externalCallIndex + 1 }
            else
              .continue
                { state with
                    world := returndataAfterCall outcome state.world
                    bindings := bindValues
                      (bindValue state.bindings successVar 0)
                      resultVars (outcome.returnValues.map wordNormalize)
                    externalCallIndex := state.externalCallIndex + 1 }
        | none => .revert
    | state, .ecm mod args =>
        match evalExprList fields state args with
        | some _ =>
            let outcome := state.externalCallOracle state.externalCallIndex
            if outcome.succeeded then
              if outcome.returnValues.length != mod.resultVars.length then .revert
              else
                .continue
                  { state with
                      world := returndataAfterCall outcome
                        (mod.committedWorld outcome.postCallWorld state.world)
                      bindings := bindValues state.bindings mod.resultVars
                        (outcome.returnValues.map wordNormalize)
                      externalCallIndex := state.externalCallIndex + 1 }
            else .revert
        | none => .revert
    | _, _ => .revert

  def execStmtList (fields : List Field) : RuntimeState → List Stmt → StmtResult
    | state, [] => .continue state
    | state, stmt :: rest =>
        match execStmt fields state stmt with
        | .continue next => execStmtList fields next rest
        | .stop next => .stop next
        | .return value next => .return value next
        | .revert => .revert
end

mutual
  @[simp] theorem execStmtWithEvents_nil_eq_execStmt
      (fields : List Field) (state : RuntimeState) (stmt : Stmt) :
      execStmtWithEvents fields [] state stmt = execStmt fields state stmt := by
    cases stmt <;>
      simp [execStmtWithEvents, execStmt, execStmtListWithEvents_nil_eq_execStmtList]

  @[simp] theorem execStmtListWithEvents_nil_eq_execStmtList
      (fields : List Field) (state : RuntimeState) (stmts : List Stmt) :
      execStmtListWithEvents fields [] state stmts = execStmtList fields state stmts := by
    cases stmts with
    | nil =>
        simp [execStmtListWithEvents, execStmtList]
    | cons stmt rest =>
        simp [execStmtListWithEvents, execStmtList, execStmtWithEvents_nil_eq_execStmt,
          execStmtListWithEvents_nil_eq_execStmtList]
end

/-! ### `Stmt.ecm` as an opaque external-world transition

An External Call Module packages a reusable external call pattern, so its source
meaning is the same oracle-driven step the `externalCallBind` lane uses: the
per-call receipt at `externalCallIndex` decides success, supplies the words bound
to `mod.resultVars`, and — only for modules the ECM framework classifies as
state-writing — supplies the committed external world. For read-only modules the
caller world is preserved except for caller-local memory and the append-only
call journal, which follow the receipt's post-call world
(`ExternalCallModule.committedWorld`). -/

/-- A module that does not write state commits no external world, matching the
`staticcall` clause of `Compiler.ECM.StatefulExternal.Summary.interprets`, but
it does commit the receipt's modeled caller-local memory effects and the
append-only call journal: a compiled `staticcall` writes its output into caller
memory (e.g. a precompile digest at the caller-supplied output offset) and
`externalCall` / `denoteCallJournaled` appends a journal entry to `calls`, so
`writesState = false` preserves every caller-world field except `memory`,
`calls` and the EIP-211 `returndata` buffer. The first two follow the receipt's
post-call world; the buffer is replaced by the receipt's return words, since a
`staticcall` still leaves its callee's return data in the caller's frame. -/
theorem execStmt_ecm_static_preserves_world_modulo_memory_calls_and_returndata
    {fields : List Field} {state next : RuntimeState}
    {mod : Compiler.ECM.ExternalCallModule} {args : List Expr}
    (hstatic : mod.writesState = false)
    (hrun : execStmt fields state (.ecm mod args) = .continue next) :
    next.world = { state.world with
      memory := ((state.externalCallOracle state.externalCallIndex).postCallWorld.getD
        state.world).memory
      calls := ((state.externalCallOracle state.externalCallIndex).postCallWorld.getD
        state.world).calls
      returndata := (state.externalCallOracle state.externalCallIndex).returnValues.map
        wordNormalize } := by
  simp only [execStmt] at hrun
  split at hrun
  · split at hrun
    · split at hrun
      · cases hrun
      · injection hrun with h
        subst h
        simp [Compiler.ECM.ExternalCallModule.committedWorld, hstatic, returndataAfterCall]
    · cases hrun
  · cases hrun

/-- Regression: a successful read-only ECM step preserves the receipt's call
journal, not the caller's. This would fail if `committedWorld` dropped
the `calls` field for `writesState = false` modules. -/
theorem execStmt_ecm_static_preserves_calls
    {fields : List Field} {state next : RuntimeState}
    {mod : Compiler.ECM.ExternalCallModule} {args : List Expr}
    (hstatic : mod.writesState = false)
    (hrun : execStmt fields state (.ecm mod args) = .continue next) :
    next.world.calls =
      ((state.externalCallOracle state.externalCallIndex).postCallWorld.getD
        state.world).calls := by
  have h := execStmt_ecm_static_preserves_world_modulo_memory_calls_and_returndata hstatic hrun
  rw [h]

/-- Every committed `.ecm` step consumes exactly one call receipt, so distinct
module invocations never observe the same oracle entry. -/
theorem execStmt_ecm_advances_call_index
    {fields : List Field} {state next : RuntimeState}
    {mod : Compiler.ECM.ExternalCallModule} {args : List Expr}
    (hrun : execStmt fields state (.ecm mod args) = .continue next) :
    next.externalCallIndex = state.externalCallIndex + 1 := by
  simp only [execStmt] at hrun
  split at hrun
  · split at hrun
    · split at hrun
      · cases hrun
      · injection hrun with h
        subst h
        rfl
    · cases hrun
  · cases hrun

/-- A committed `.ecm` step binds exactly the module's declared result variables
to the normalized receipt words. -/
theorem execStmt_ecm_binds_resultVars
    {fields : List Field} {state next : RuntimeState}
    {mod : Compiler.ECM.ExternalCallModule} {args : List Expr}
    (hrun : execStmt fields state (.ecm mod args) = .continue next) :
    next.bindings =
      bindValues state.bindings mod.resultVars
        ((state.externalCallOracle state.externalCallIndex).returnValues.map wordNormalize) := by
  simp only [execStmt] at hrun
  split at hrun
  · split at hrun
    · split at hrun
      · cases hrun
      · injection hrun with h
        subst h
        rfl
    · cases hrun
  · cases hrun

/-- A failing call receipt reverts the `.ecm` step; the module never observes a
partially applied external transition. -/
theorem execStmt_ecm_reverts_of_receipt_failure
    (fields : List Field) (state : RuntimeState)
    (mod : Compiler.ECM.ExternalCallModule) (args : List Expr)
    (hfail : (state.externalCallOracle state.externalCallIndex).succeeded = false) :
    execStmt fields state (.ecm mod args) = .revert := by
  simp only [execStmt]
  split
  · simp [hfail]
  · rfl

mutual
  /-- Source execution of a contract-surface-closed statement is agnostic to
  the event catalog: `execStmtWithEvents` and `execStmt` differ only in the
  `.emit` arm, which the plain contract-surface gate excludes. -/
  theorem execStmtWithEvents_eq_execStmt_of_contractSurfaceClosed
      (fields : List Field) (events : List EventDef) (stmt : Stmt)
      (hsurface : stmtTouchesUnsupportedContractSurface stmt = false)
      (state : RuntimeState) :
      execStmtWithEvents fields events state stmt = execStmt fields state stmt := by
    cases stmt
    case ite cond thenBranch elseBranch =>
        simp only [stmtTouchesUnsupportedContractSurface,
          Bool.or_eq_false_iff] at hsurface
        simp [execStmtWithEvents, execStmt,
          execStmtListWithEvents_eq_execStmtList_of_contractSurfaceClosed
            fields events thenBranch hsurface.1.2,
          execStmtListWithEvents_eq_execStmtList_of_contractSurfaceClosed
            fields events elseBranch hsurface.2]
    case forEach varName count body =>
        simp [execStmtWithEvents, execStmt,
          execStmtListWithEvents_eq_execStmtList_of_contractSurfaceClosed
            fields events body
            (stmtListTouchesUnsupportedContractSurface_of_forEach_surfaceClosed
              hsurface)]
    case forEachSetBit =>
        simp [stmtTouchesUnsupportedContractSurface] at hsurface
    case emit eventName args =>
        simp [stmtTouchesUnsupportedContractSurface] at hsurface
    all_goals simp [execStmtWithEvents, execStmt]

  /-- List version of
  `execStmtWithEvents_eq_execStmt_of_contractSurfaceClosed`. -/
  theorem execStmtListWithEvents_eq_execStmtList_of_contractSurfaceClosed
      (fields : List Field) (events : List EventDef) (stmts : List Stmt)
      (hsurface : stmtListTouchesUnsupportedContractSurface stmts = false)
      (state : RuntimeState) :
      execStmtListWithEvents fields events state stmts =
        execStmtList fields state stmts := by
    cases stmts with
    | nil => simp [execStmtListWithEvents, execStmtList]
    | cons stmt rest =>
        simp only [stmtListTouchesUnsupportedContractSurface,
          Bool.or_eq_false_iff] at hsurface
        simp [execStmtListWithEvents, execStmtList,
          execStmtWithEvents_eq_execStmt_of_contractSurfaceClosed
            fields events stmt hsurface.1,
          execStmtListWithEvents_eq_execStmtList_of_contractSurfaceClosed
            fields events rest hsurface.2]
end

structure SourceContractResult where
  success : Bool
  returnValue : Option Nat
  finalStorage : Nat → Nat
  events : List (List Nat)

structure InternalFunctionResult where
  success : Bool
  returnValue : Option Nat
  world : Verity.ContractState

def revertedResult (spec : CompilationModel) (initialWorld : Verity.ContractState) :
    SourceContractResult :=
  { success := false
    returnValue := none
    finalStorage := encodeStorage spec initialWorld
    events := encodeEvents initialWorld.events }

def successResult (spec : CompilationModel) (world : Verity.ContractState) (ret : Option Nat) :
    SourceContractResult :=
  { success := true
    returnValue := ret
    finalStorage := encodeStorage spec world
    events := encodeEvents world.events }

def revertedInternalResult (initialWorld : Verity.ContractState) :
    InternalFunctionResult :=
  { success := false
    returnValue := none
    world := initialWorld }

def successInternalResult (world : Verity.ContractState) (ret : Option Nat) :
    InternalFunctionResult :=
  { success := true
    returnValue := ret
    world := world }

def bindSupportedParams (params : List Param) (args : List Nat) :
    Option (List (String × Nat)) :=
  match params, args with
  | [], _ => some []
  | _ :: _, [] => none
  | param :: rest, arg :: restArgs => do
      let value ← decodeSupportedParamWord param.ty arg
      let bindings ← bindSupportedParams rest restArgs
      pure ((param.name, value) :: bindings)

def bindExternalParam (selector : Nat) (calldata : List Nat)
    (headSize baseOffset headOffset : Nat) (param : Param) :
    Option (List (String × Nat)) :=
  DynamicAbi.bindExternalParam selector calldata headSize baseOffset headOffset param

def bindExternalParamsFrom (selector : Nat) (calldata : List Nat)
    (headSize baseOffset : Nat) (params : List Param) (headOffset : Nat) :
    Option (List (String × Nat)) :=
  DynamicAbi.bindExternalParamsFrom selector calldata headSize baseOffset params headOffset

def bindExternalParams (selector : Nat) (params : List Param) (calldata : List Nat) :
    Option (List (String × Nat)) :=
  DynamicAbi.bindExternalParams selector params calldata

theorem decodeSupportedParamWord_eq_dynamicAbi (ty : ParamType) (word : Nat) :
    decodeSupportedParamWord ty word = DynamicAbi.decodeSupportedParamWord ty word := by
  cases ty <;> rfl

theorem bindSupportedParams_eq_dynamicAbi :
    ∀ (params : List Param) (args : List Nat),
      bindSupportedParams params args = DynamicAbi.bindSupportedParams params args
  | [], _ => rfl
  | _ :: _, [] => rfl
  | param :: rest, arg :: restArgs => by
      simp only [bindSupportedParams, DynamicAbi.bindSupportedParams,
        decodeSupportedParamWord_eq_dynamicAbi, bindSupportedParams_eq_dynamicAbi rest restArgs]

theorem bindSupportedParams_some_length
    {params : List Param} {args : List Nat} {bindings : List (String × Nat)}
    (hbind : bindSupportedParams params args = some bindings) :
    params.length ≤ args.length := by
  induction params generalizing args bindings with
  | nil =>
      exact Nat.zero_le _
  | cons param rest ih =>
      cases args with
      | nil =>
          simp [bindSupportedParams] at hbind
      | cons arg restArgs =>
          cases hdecode : decodeSupportedParamWord param.ty arg <;>
              simp [bindSupportedParams, hdecode] at hbind
          case some value =>
            cases hrest : bindSupportedParams rest restArgs <;>
                simp [hrest] at hbind
            case some restBindings =>
              cases hbind
              exact Nat.succ_le_succ (ih hrest)

@[simp] theorem bindExternalParams_eq_some_of_bindSupportedParams
    {params : List Param} {args : List Nat} {bindings : List (String × Nat)}
    (selector : Nat)
    (hbind : bindSupportedParams params args = some bindings) :
    bindExternalParams selector params args = some bindings := by
  have hlen := bindSupportedParams_some_length hbind
  simp only [bindExternalParams, DynamicAbi.bindExternalParams, hlen, ↓reduceIte]
  rw [← bindSupportedParams_eq_dynamicAbi, hbind]

@[simp] theorem bindExternalParams_eq_none_of_not_length_le
    {params : List Param} {args : List Nat}
    (selector : Nat)
    (hlen : ¬ params.length ≤ args.length) :
    bindExternalParams selector params args = none := by
  simp only [bindExternalParams, DynamicAbi.bindExternalParams, hlen, ↓reduceIte]

theorem bindSupportedParams_take_param_length
    {params : List Param}
    {args : List Nat}
    {bindings : List (String × Nat)}
    (hbind : bindSupportedParams params args = some bindings) :
    bindSupportedParams params (args.take params.length) = some bindings := by
  induction params generalizing args bindings with
  | nil =>
      simpa [bindSupportedParams] using hbind
  | cons param rest ih =>
      cases args with
      | nil =>
          simp [bindSupportedParams] at hbind
      | cons arg restArgs =>
          simp only [bindSupportedParams, List.length_cons, List.take] at hbind ⊢
          cases hdecode : decodeSupportedParamWord param.ty arg <;> simp [hdecode] at hbind ⊢
          rename_i value
          cases htail : bindSupportedParams rest restArgs with
          | none =>
              simp [htail] at hbind
          | some tailBindings =>
              simp [htail] at hbind ⊢
              cases hbind
              simp [ih htail]

def withTransactionContext (world : Verity.ContractState) (tx : IRTransaction) :
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
    calldata := tx.args
    returndata := [] }

def withConstructorTransactionContext (world : Verity.ContractState) (tx : IRTransaction) :
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
    calldataSize := Verity.Core.Uint256.ofNat (tx.args.length * 32)
    calldata := tx.args
    returndata := [] }

/-- EIP-211 makes the returndata buffer frame-local: every transaction frame
    starts empty, so a buffer left over from an earlier execution (e.g. a
    post-state world) cannot be observed by this frame's `returndatasize()`. -/
@[simp] theorem returndata_withTransactionContext
    (world : Verity.ContractState) (tx : IRTransaction) :
    (withTransactionContext world tx).returndata = [] := rfl

/-- The constructor frame enters with an empty EIP-211 buffer as well. -/
@[simp] theorem returndata_withConstructorTransactionContext
    (world : Verity.ContractState) (tx : IRTransaction) :
    (withConstructorTransactionContext world tx).returndata = [] := rfl

/-- Call-frame updates keep `storageWords`, so the storage views are unchanged. -/
@[simp] theorem storage_withTransactionContext
    (world : Verity.ContractState) (tx : IRTransaction) :
    (withTransactionContext world tx).storage = world.storage := by
  funext slot
  simp [withTransactionContext, Verity.ContractState.storage]

@[simp] theorem storageAddr_withTransactionContext
    (world : Verity.ContractState) (tx : IRTransaction) :
    (withTransactionContext world tx).storageAddr = world.storageAddr := by
  funext slot
  simp [withTransactionContext, Verity.ContractState.storageAddr]

@[simp] theorem storageArray_withTransactionContext
    (world : Verity.ContractState) (tx : IRTransaction) :
    (withTransactionContext world tx).storageArray = world.storageArray := rfl

@[simp] theorem storage_withConstructorTransactionContext
    (world : Verity.ContractState) (tx : IRTransaction) :
    (withConstructorTransactionContext world tx).storage = world.storage := by
  funext slot
  simp [withConstructorTransactionContext, Verity.ContractState.storage]

@[simp] theorem storageAddr_withConstructorTransactionContext
    (world : Verity.ContractState) (tx : IRTransaction) :
    (withConstructorTransactionContext world tx).storageAddr = world.storageAddr := by
  funext slot
  simp [withConstructorTransactionContext, Verity.ContractState.storageAddr]

@[simp] theorem storageArray_withConstructorTransactionContext
    (world : Verity.ContractState) (tx : IRTransaction) :
    (withConstructorTransactionContext world tx).storageArray = world.storageArray := rfl

@[simp] theorem transientStorage_withConstructorTransactionContext
    (world : Verity.ContractState) (tx : IRTransaction) :
    (withConstructorTransactionContext world tx).transientStorage = world.transientStorage := rfl

@[simp] theorem transientStorage_at_withConstructorTransactionContext
    (world : Verity.ContractState) (tx : IRTransaction) (slot : Nat) :
    (withConstructorTransactionContext world tx).transientStorage slot =
      world.transientStorage slot := rfl

theorem findDynamicArrayElementAtSlot_withTransactionContext
    (fields : List Field)
    (world : Verity.ContractState)
    (tx : IRTransaction)
    (slot : Nat) :
    findDynamicArrayElementAtSlot fields (withTransactionContext world tx) slot =
      findDynamicArrayElementAtSlot fields world slot := by
  unfold findDynamicArrayElementAtSlot
  suffices
      ∀ remaining idx,
        findDynamicArrayElementAtSlot.go (withTransactionContext world tx) slot remaining idx =
          findDynamicArrayElementAtSlot.go world slot remaining idx by
    simpa using this fields 0
  intro remaining idx
  induction remaining generalizing idx with
  | nil =>
      rfl
  | cons field rest ih =>
      cases hty : field.ty with
      | uint256 =>
          simpa [findDynamicArrayElementAtSlot.go, withTransactionContext, hty] using ih (idx + 1)
      | address =>
          simpa [findDynamicArrayElementAtSlot.go, withTransactionContext, hty] using ih (idx + 1)
      | fixedArrayUint128 size =>
          simpa [findDynamicArrayElementAtSlot.go, withTransactionContext, hty] using ih (idx + 1)
      | adt name maxFields =>
          simpa [findDynamicArrayElementAtSlot.go, withTransactionContext, hty] using ih (idx + 1)
      | dynamicArray elemType =>
          cases hscan :
              findDynamicArrayElementAtSlot.scanElements slot
                (field.slot.getD idx)
                (world.storageArray (field.slot.getD idx)) 0 with
          | none =>
              simpa [findDynamicArrayElementAtSlot.go, withTransactionContext, hty, hscan] using
                ih (idx + 1)
          | some value =>
              simp [findDynamicArrayElementAtSlot.go, withTransactionContext, hty, hscan]
      | mappingTyped mt =>
          simpa [findDynamicArrayElementAtSlot.go, withTransactionContext, hty] using ih (idx + 1)
      | mappingStruct keyType members =>
          simpa [findDynamicArrayElementAtSlot.go, withTransactionContext, hty] using ih (idx + 1)
      | mappingStruct2 outerKey innerKey members =>
          simpa [findDynamicArrayElementAtSlot.go, withTransactionContext, hty] using ih (idx + 1)
      | mappingFixedArray keyType size =>
          simpa [findDynamicArrayElementAtSlot.go, withTransactionContext, hty] using ih (idx + 1)

theorem findDynamicArrayElementAtSlot_congr_storageArray
    (fields : List Field)
    (world1 world2 : Verity.ContractState)
    (slot : Nat)
    (h_storageArray : world1.storageArray = world2.storageArray) :
    findDynamicArrayElementAtSlot fields world1 slot =
      findDynamicArrayElementAtSlot fields world2 slot := by
  unfold findDynamicArrayElementAtSlot
  suffices
      ∀ remaining idx,
        findDynamicArrayElementAtSlot.go world1 slot remaining idx =
          findDynamicArrayElementAtSlot.go world2 slot remaining idx by
    simpa using this fields 0
  intro remaining idx
  induction remaining generalizing idx with
  | nil =>
      rfl
  | cons field rest ih =>
      cases hty : field.ty with
      | uint256 =>
          simpa [findDynamicArrayElementAtSlot.go, hty] using ih (idx + 1)
      | address =>
          simpa [findDynamicArrayElementAtSlot.go, hty] using ih (idx + 1)
      | fixedArrayUint128 size =>
          simpa [findDynamicArrayElementAtSlot.go, hty] using ih (idx + 1)
      | adt name maxFields =>
          simpa [findDynamicArrayElementAtSlot.go, hty] using ih (idx + 1)
      | dynamicArray elemType =>
          cases hscan :
              findDynamicArrayElementAtSlot.scanElements slot
                (field.slot.getD idx)
                (world2.storageArray (field.slot.getD idx)) 0 with
          | none =>
              simp only [findDynamicArrayElementAtSlot.go, hty, h_storageArray, hscan]
              exact ih (idx + 1)
          | some value =>
              simp [findDynamicArrayElementAtSlot.go, hty, h_storageArray, hscan]
      | mappingTyped mt =>
          simpa [findDynamicArrayElementAtSlot.go, hty] using ih (idx + 1)
      | mappingStruct keyType members =>
          simpa [findDynamicArrayElementAtSlot.go, hty] using ih (idx + 1)
      | mappingStruct2 outerKey innerKey members =>
          simpa [findDynamicArrayElementAtSlot.go, hty] using ih (idx + 1)
      | mappingFixedArray keyType size =>
          simpa [findDynamicArrayElementAtSlot.go, hty] using ih (idx + 1)

theorem encodeStorageAt_congr
    {fields : List Field}
    {world1 world2 : Verity.ContractState}
    {slot : Nat}
    (h_storage : world1.storage slot = world2.storage slot)
    (h_storageAddr : world1.storageAddr slot = world2.storageAddr slot)
    (h_storageArray : world1.storageArray = world2.storageArray) :
    encodeStorageAt fields world1 slot = encodeStorageAt fields world2 slot := by
  unfold encodeStorageAt
  split
  · simp [h_storage, h_storageAddr, h_storageArray]
  · rw [findDynamicArrayElementAtSlot_congr_storageArray fields world1 world2 slot h_storageArray]
    simp [h_storage]

@[simp] theorem encodeStorageAt_withTransactionContext
    (fields : List Field)
    (world : Verity.ContractState)
    (tx : IRTransaction)
    (slot : Nat) :
    encodeStorageAt fields (withTransactionContext world tx) slot =
      encodeStorageAt fields world slot := by
  unfold encodeStorageAt
  split
  · simp
  · rw [findDynamicArrayElementAtSlot_withTransactionContext]
    simp

@[simp] theorem encodeStorage_withTransactionContext
    (spec : CompilationModel)
    (world : Verity.ContractState)
    (tx : IRTransaction) :
    encodeStorage spec (withTransactionContext world tx) =
      encodeStorage spec world := by
  funext slot
  simpa [encodeStorage] using
    encodeStorageAt_withTransactionContext (effectiveFields spec) world tx slot

@[simp] theorem encodeStorageAt_withConstructorTransactionContext
    (fields : List Field)
    (world : Verity.ContractState)
    (tx : IRTransaction)
    (slot : Nat) :
    encodeStorageAt fields (withConstructorTransactionContext world tx) slot =
      encodeStorageAt fields world slot := by
  exact encodeStorageAt_congr
    (fields := fields)
    (world1 := withConstructorTransactionContext world tx)
    (world2 := world)
    (slot := slot)
    (by simp)
    (by simp)
    (by simp [withConstructorTransactionContext])

@[simp] theorem encodeStorage_withConstructorTransactionContext
    (spec : CompilationModel)
    (world : Verity.ContractState)
    (tx : IRTransaction) :
    encodeStorage spec (withConstructorTransactionContext world tx) =
      encodeStorage spec world := by
  funext slot
  simpa [encodeStorage] using
    encodeStorageAt_withConstructorTransactionContext (effectiveFields spec) world tx slot

def selectorFunctionPairs (spec : CompilationModel) (selectors : List Nat) :
    List (FunctionSpec × Nat) :=
  (selectorDispatchedFunctions spec).zip selectors

def findFunctionBySelector (spec : CompilationModel) (selectors : List Nat) (selector : Nat) :
    Option FunctionSpec :=
  (selectorFunctionPairs spec selectors).find? (fun entry => entry.2 == selector) |>.map Prod.fst

def constructorArgAliasValue?
    (param : Param)
    (rawArgs : List Nat)
    (headWord : Nat)
    (bindings : List (String × Nat)) :
    Option Nat :=
  if isDynamicParamType param.ty then
    rawArgs[headWord]? |> Option.map wordNormalize
  else
    match param.ty with
    | .uint256 | .int256 | .uint8 | .uint16 | .address | .bool | .bytes32 =>
        lookupBinding? bindings param.name
    | _ =>
        rawArgs[headWord]? |> Option.map wordNormalize

def bindConstructorArgAliasesFrom
    (remaining : List Param)
    (rawArgs : List Nat)
    (idx : Nat)
    (headWord : Nat)
    (bindings : List (String × Nat)) :
    Option (List (String × Nat)) :=
  match remaining with
  | [] => some bindings
  | param :: rest =>
      match constructorArgAliasValue? param rawArgs headWord bindings with
      | none => none
      | some value =>
          if (bindings.map Prod.fst).contains s!"arg{idx}" then
            none
          else
            bindConstructorArgAliasesFrom rest rawArgs (idx + 1)
              (headWord + paramHeadSize param.ty / 32)
              (bindValue bindings s!"arg{idx}" value)

def bindConstructorArgAliases
    (params : List Param)
    (rawArgs : List Nat)
    (bindings : List (String × Nat)) :
    Option (List (String × Nat)) :=
  bindConstructorArgAliasesFrom params rawArgs 0 0 bindings

theorem bindConstructorArgAliasesFrom_preserves_lookup
    {remaining : List Param}
    {rawArgs : List Nat}
    {idx headWord : Nat}
    {bindings out : List (String × Nat)}
    {queryName : String}
    (hbind :
      bindConstructorArgAliasesFrom remaining rawArgs idx headWord bindings = some out)
    (hexists : ∃ v, lookupBinding? bindings queryName = some v) :
    ∃ v, lookupBinding? out queryName = some v := by
  induction remaining generalizing idx headWord bindings out with
  | nil =>
      simp [bindConstructorArgAliasesFrom] at hbind
      cases hbind
      exact hexists
  | cons param rest ih =>
      simp [bindConstructorArgAliasesFrom] at hbind
      cases hvalue : constructorArgAliasValue? param rawArgs headWord bindings <;>
        simp [hvalue] at hbind
      case some value =>
        exact ih hbind.2
          (lookupBinding?_bindValue_exists bindings s!"arg{idx}" queryName value hexists)

theorem bindConstructorArgAliasesFrom_argAlias_present
    {remaining : List Param}
    {rawArgs : List Nat}
    {idx headWord target : Nat}
    {bindings out : List (String × Nat)}
    (hbind :
      bindConstructorArgAliasesFrom remaining rawArgs idx headWord bindings = some out)
    (hlo : idx ≤ target)
    (hhi : target < idx + remaining.length) :
  ∃ v, lookupBinding? out s!"arg{target}" = some v := by
  induction remaining generalizing idx headWord bindings out with
  | nil =>
      simp at hhi
      omega
  | cons param rest ih =>
      have hhi' : target < idx + (rest.length + 1) := by
        simpa using hhi
      simp [bindConstructorArgAliasesFrom] at hbind
      cases hvalue : constructorArgAliasValue? param rawArgs headWord bindings <;>
        simp [hvalue] at hbind
      case some value =>
        by_cases htarget : target = idx
        · have hcurrent :
              ∃ v, lookupBinding?
                (bindValue bindings s!"arg{idx}" value) s!"arg{target}" = some v := by
            rw [htarget]
            exact ⟨value, by simp [lookupBinding?, bindValue]⟩
          exact bindConstructorArgAliasesFrom_preserves_lookup hbind.2 hcurrent
        · have hnextLo : idx + 1 ≤ target := by omega
          have hnextHi : target < idx + 1 + rest.length := by omega
          exact ih hbind.2 hnextLo hnextHi

theorem bindConstructorArgAliases_argAlias_present
    {params : List Param}
    {rawArgs : List Nat}
    {bindings out : List (String × Nat)}
    {idx : Nat}
    (hbind : bindConstructorArgAliases params rawArgs bindings = some out)
    (hidx : idx < params.length) :
    ∃ v, lookupBinding? out s!"arg{idx}" = some v := by
  exact bindConstructorArgAliasesFrom_argAlias_present
    (remaining := params)
    (rawArgs := rawArgs)
    (idx := 0)
    (headWord := 0)
    (target := idx)
    (bindings := bindings)
    (out := out)
    (by simpa [bindConstructorArgAliases] using hbind)
    (Nat.zero_le idx)
    (by simpa using hidx)

def constructorExecutionBindings
    (ctor : ConstructorSpec)
    (rawArgs : List Nat) :
    Option (List (String × Nat)) :=
  match bindSupportedParams ctor.params (rawArgs.take ctor.params.length) with
  | none => none
  | some bindings =>
      bindConstructorArgAliases ctor.params rawArgs bindings

theorem constructorExecutionBindings_argAlias_present
    {ctor : ConstructorSpec}
    {rawArgs : List Nat}
    {bindings : List (String × Nat)}
    {idx : Nat}
    (hbind : constructorExecutionBindings ctor rawArgs = some bindings)
    (hidx : idx < ctor.params.length) :
    ∃ v, lookupBinding? bindings s!"arg{idx}" = some v := by
  unfold constructorExecutionBindings at hbind
  cases hparams :
      bindSupportedParams ctor.params (rawArgs.take ctor.params.length) with
  | none =>
      simp [hparams] at hbind
  | some decoded =>
      exact bindConstructorArgAliases_argAlias_present
        (params := ctor.params)
        (rawArgs := rawArgs)
        (bindings := decoded)
        (out := bindings)
        (idx := idx)
        (by simpa [hparams] using hbind)
        hidx

def directHelperTouchesUnsupportedConstructorRawCalldataSurface
    (spec : CompilationModel)
    (fn : FunctionSpec) : Bool :=
  (helperCallNames fn).any fun calleeName =>
    match findUniqueInternalFunction? spec calleeName with
    | some callee =>
        stmtListTouchesUnsupportedConstructorRawCalldataSurface callee.body
    | none => true

def helperClosureTouchesUnsupportedConstructorRawCalldataSurfaceFrom
    (spec : CompilationModel) : Nat → List String → FunctionSpec → Bool
  | 0, _, _ => false
  | fuel + 1, visited, fn =>
      if fn.name ∈ visited then
        false
      else
        (helperCallNames fn).any fun calleeName =>
          match findUniqueInternalFunction? spec calleeName with
          | some callee =>
              stmtListTouchesUnsupportedConstructorRawCalldataSurface callee.body ||
                helperClosureTouchesUnsupportedConstructorRawCalldataSurfaceFrom spec fuel
                  (fn.name :: visited) callee
          | none => true

def helperClosureTouchesUnsupportedConstructorRawCalldataSurface
    (spec : CompilationModel) (fuel : Nat) (fn : FunctionSpec) : Bool :=
  helperClosureTouchesUnsupportedConstructorRawCalldataSurfaceFrom spec fuel [] fn

def constructorTouchesUnsupportedRawCalldataSurface
    (spec : CompilationModel)
    (ctor : ConstructorSpec) : Bool :=
  stmtListTouchesUnsupportedConstructorRawCalldataSurface ctor.body ||
    helperClosureTouchesUnsupportedConstructorRawCalldataSurface spec
      (spec.functions.length + 1)
      (constructorAsFunctionSpec ctor)

def interpretFunction (spec : CompilationModel) (fn : FunctionSpec)
    (tx : IRTransaction) (initialWorld : Verity.ContractState)
    (externalCallOracle : Nat → ExternalCallOutcome := fun _ => ⟨false, [], none⟩) :
    SourceContractResult :=
  let worldWithTx := withTransactionContext initialWorld tx
  let fields := effectiveFields spec
  match bindExternalParams tx.functionSelector fn.params tx.args with
  | none => revertedResult spec worldWithTx
  | some bindings =>
      match execStmtListWithEvents fields spec.events
          { world := worldWithTx, bindings := bindings, selector := tx.functionSelector,
            externalCallOracle := externalCallOracle } fn.body with
      | .continue state => successResult spec state.world none
      | .stop state => successResult spec state.world none
      | .return value state => successResult spec state.world (some value)
      | .revert => revertedResult spec worldWithTx

def interpretConstructor (spec : CompilationModel) (ctor : ConstructorSpec)
    (tx : IRTransaction) (initialWorld : Verity.ContractState)
    (externalCallOracle : Nat → ExternalCallOutcome := fun _ => ⟨false, [], none⟩) :
    SourceContractResult :=
  let constructorWorldWithTx := withTransactionContext initialWorld tx
  let fields := effectiveFields spec
  if constructorTouchesUnsupportedRawCalldataSurface spec ctor then
    revertedResult spec constructorWorldWithTx
  else
    match constructorExecutionBindings ctor tx.args with
    | none => revertedResult spec constructorWorldWithTx
    | some bindings =>
        match execStmtListWithEvents fields spec.events
            { world := constructorWorldWithTx, bindings := bindings,
              selector := tx.functionSelector,
              externalCallOracle := externalCallOracle }
            ctor.body with
        | .continue state => successResult spec state.world none
        | .stop state => successResult spec state.world none
        | .return value state => successResult spec state.world (some value)
        | .revert => revertedResult spec constructorWorldWithTx

def interpretContract (spec : CompilationModel) (selectors : List Nat)
    (tx : IRTransaction) (initialWorld : Verity.ContractState)
    (externalCallOracle : Nat → ExternalCallOutcome := fun _ => ⟨false, [], none⟩) :
    SourceContractResult :=
  match findFunctionBySelector spec selectors tx.functionSelector with
  | some fn =>
      if !fn.isPayable && tx.msgValue % Compiler.Constants.evmModulus != 0 then
        revertedResult spec (withTransactionContext initialWorld tx)
      else
        interpretFunction spec fn tx initialWorld externalCallOracle
  | none => revertedResult spec (withTransactionContext initialWorld tx)

-- The ceilDiv case pushes the equation-compiler's `simp` past 200 000 heartbeats.
set_option maxHeartbeats 400000 in
mutual
  /-- Spec-aware source semantics for the next helper-proof step.
  This is additive: the current generic theorem still reasons about the
  helper-free `interpretFunction` / `interpretContract` path above. -/
  def evalExprWithHelpers
      (spec : CompilationModel)
      (fields : List Field)
      (fuel : Nat)
      (state : RuntimeState) : Expr → Option Nat
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
              some (state.world.transientStorage (wordNormalize slot)).val
            else
              some (state.world.storageAddr (wordNormalize slot)).val
        | none => none
    | .storageArrayLength fieldName =>
        match findFieldWithResolvedSlot fields fieldName with
        | some ({ ty := .dynamicArray _, .. }, slot) => some (state.world.storageArray slot).length
        | _ => none
    | .storageArrayElement fieldName index => do
        let idx ← evalExprWithHelpers spec fields fuel state index
        match findFieldWithResolvedSlot fields fieldName with
        | some ({ ty := .dynamicArray _, .. }, slot) =>
            match (state.world.storageArray slot)[idx]? with
            | some value => some value.val
            | none => none
        | some ({ ty := .fixedArrayUint128 size, .. }, slot) =>
            readFixedUint128ArrayElement state.world slot size idx
        | _ => none
    | .constructorArg idx =>
        lookupBinding? state.bindings s!"arg{idx}"
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
    | .returndataSize => some state.world.returndataSize
    | .localVar name => some (lookupValue state.bindings name)
    | .add a b => do
        let lhs : Verity.Core.Uint256 := ← evalExprWithHelpers spec fields fuel state a
        let rhs : Verity.Core.Uint256 := ← evalExprWithHelpers spec fields fuel state b
        pure (lhs + rhs).val
    | .sub a b => do
        let lhs : Verity.Core.Uint256 := ← evalExprWithHelpers spec fields fuel state a
        let rhs : Verity.Core.Uint256 := ← evalExprWithHelpers spec fields fuel state b
        pure (lhs - rhs).val
    | .mul a b => do
        let lhs : Verity.Core.Uint256 := ← evalExprWithHelpers spec fields fuel state a
        let rhs : Verity.Core.Uint256 := ← evalExprWithHelpers spec fields fuel state b
        pure (lhs * rhs).val
    | .div a b => do
        let lhs : Verity.Core.Uint256 := ← evalExprWithHelpers spec fields fuel state a
        let rhs : Verity.Core.Uint256 := ← evalExprWithHelpers spec fields fuel state b
        pure (lhs / rhs).val
    | .mod a b => do
        let lhs : Verity.Core.Uint256 := ← evalExprWithHelpers spec fields fuel state a
        let rhs : Verity.Core.Uint256 := ← evalExprWithHelpers spec fields fuel state b
        pure (lhs % rhs).val
    | .bitAnd a b => do
        let lhs ← evalExprWithHelpers spec fields fuel state a
        let rhs ← evalExprWithHelpers spec fields fuel state b
        pure (Verity.Core.Uint256.and lhs rhs).val
    | .bitOr a b => do
        let lhs ← evalExprWithHelpers spec fields fuel state a
        let rhs ← evalExprWithHelpers spec fields fuel state b
        pure (Verity.Core.Uint256.or lhs rhs).val
    | .bitXor a b => do
        let lhs ← evalExprWithHelpers spec fields fuel state a
        let rhs ← evalExprWithHelpers spec fields fuel state b
        pure (Verity.Core.Uint256.xor lhs rhs).val
    | .bitNot a => do
        let value ← evalExprWithHelpers spec fields fuel state a
        pure (Verity.Core.Uint256.not value).val
    | .eq a b => do
        let lhs ← evalExprWithHelpers spec fields fuel state a
        let rhs ← evalExprWithHelpers spec fields fuel state b
        pure (boolWord (decide (lhs = rhs)))
    | .ge a b => do
        let lhs ← evalExprWithHelpers spec fields fuel state a
        let rhs ← evalExprWithHelpers spec fields fuel state b
        pure (boolWord (decide (rhs ≤ lhs)))
    | .gt a b => do
        let lhs ← evalExprWithHelpers spec fields fuel state a
        let rhs ← evalExprWithHelpers spec fields fuel state b
        pure (boolWord (decide (rhs < lhs)))
    | .lt a b => do
        let lhs ← evalExprWithHelpers spec fields fuel state a
        let rhs ← evalExprWithHelpers spec fields fuel state b
        pure (boolWord (decide (lhs < rhs)))
    | .le a b => do
        let lhs ← evalExprWithHelpers spec fields fuel state a
        let rhs ← evalExprWithHelpers spec fields fuel state b
        pure (boolWord (decide (lhs ≤ rhs)))
    | .logicalAnd a b => do
        let lhs ← evalExprWithHelpers spec fields fuel state a
        let rhs ← evalExprWithHelpers spec fields fuel state b
        pure (boolWord (decide (lhs != 0) && decide (rhs != 0)))
    | .logicalOr a b => do
        let lhs ← evalExprWithHelpers spec fields fuel state a
        let rhs ← evalExprWithHelpers spec fields fuel state b
        pure (boolWord (decide (lhs != 0) || decide (rhs != 0)))
    | .logicalNot a => do
        let value ← evalExprWithHelpers spec fields fuel state a
        pure (boolWord (decide (value = 0)))
    | .min a b => do
        let lhs ← evalExprWithHelpers spec fields fuel state a
        let rhs ← evalExprWithHelpers spec fields fuel state b
        pure (if lhs ≤ rhs then lhs else rhs)
    | .max a b => do
        let lhs ← evalExprWithHelpers spec fields fuel state a
        let rhs ← evalExprWithHelpers spec fields fuel state b
        pure (if rhs ≤ lhs then lhs else rhs)
    | .wMulDown a b => do
        let lhs : Verity.Core.Uint256 := ← evalExprWithHelpers spec fields fuel state a
        let rhs : Verity.Core.Uint256 := ← evalExprWithHelpers spec fields fuel state b
        let wad : Verity.Core.Uint256 := 1000000000000000000
        pure ((lhs * rhs) / wad).val
    | .wDivUp a b => do
        let lhs : Verity.Core.Uint256 := ← evalExprWithHelpers spec fields fuel state a
        let rhs : Verity.Core.Uint256 := ← evalExprWithHelpers spec fields fuel state b
        let wad : Verity.Core.Uint256 := 1000000000000000000
        pure (((lhs * wad) + (rhs - 1)) / rhs).val
    | .ceilDiv a b => do
        let lhs : Verity.Core.Uint256 := ← evalExprWithHelpers spec fields fuel state a
        let rhs : Verity.Core.Uint256 := ← evalExprWithHelpers spec fields fuel state b
        pure (ceilDivVal lhs rhs)
    | .mulDivDown a b c => do
        let lhs : Verity.Core.Uint256 := ← evalExprWithHelpers spec fields fuel state a
        let rhs : Verity.Core.Uint256 := ← evalExprWithHelpers spec fields fuel state b
        let denom : Verity.Core.Uint256 := ← evalExprWithHelpers spec fields fuel state c
        pure ((lhs * rhs) / denom).val
    | .mulDivUp a b c => do
        let lhs : Verity.Core.Uint256 := ← evalExprWithHelpers spec fields fuel state a
        let rhs : Verity.Core.Uint256 := ← evalExprWithHelpers spec fields fuel state b
        let denom : Verity.Core.Uint256 := ← evalExprWithHelpers spec fields fuel state c
        pure (((lhs * rhs) + (denom - 1)) / denom).val
    | .ite cond thenVal elseVal => do
        let condVal ← evalExprWithHelpers spec fields fuel state cond
        if condVal != 0 then
          evalExprWithHelpers spec fields fuel state thenVal
        else
          evalExprWithHelpers spec fields fuel state elseVal
    | .shl shift value => do
        let shiftVal ← evalExprWithHelpers spec fields fuel state shift
        let wordVal ← evalExprWithHelpers spec fields fuel state value
        pure (Verity.Core.Uint256.shl shiftVal wordVal).val
    | .shr shift value => do
        let shiftVal ← evalExprWithHelpers spec fields fuel state shift
        let wordVal ← evalExprWithHelpers spec fields fuel state value
        pure (Verity.Core.Uint256.shr shiftVal wordVal).val
    | .slt a b => do
        let lhs ← evalExprWithHelpers spec fields fuel state a
        let rhs ← evalExprWithHelpers spec fields fuel state b
        pure (boolWord (decide (
          (Verity.Core.Int256.ofUint256 (Verity.Core.Uint256.ofNat lhs) : Int) <
          (Verity.Core.Int256.ofUint256 (Verity.Core.Uint256.ofNat rhs) : Int))))
    | .sgt a b => do
        let lhs ← evalExprWithHelpers spec fields fuel state a
        let rhs ← evalExprWithHelpers spec fields fuel state b
        pure (boolWord (decide (
          (Verity.Core.Int256.ofUint256 (Verity.Core.Uint256.ofNat rhs) : Int) <
          (Verity.Core.Int256.ofUint256 (Verity.Core.Uint256.ofNat lhs) : Int))))
    | .sdiv a b => do
        let lhs ← evalExprWithHelpers spec fields fuel state a
        let rhs ← evalExprWithHelpers spec fields fuel state b
        pure (Verity.Core.Int256.div
          (Verity.Core.Int256.ofUint256 (Verity.Core.Uint256.ofNat lhs))
          (Verity.Core.Int256.ofUint256 (Verity.Core.Uint256.ofNat rhs))).toUint256.val
    | .smod a b => do
        let lhs ← evalExprWithHelpers spec fields fuel state a
        let rhs ← evalExprWithHelpers spec fields fuel state b
        pure (Verity.Core.Int256.mod
          (Verity.Core.Int256.ofUint256 (Verity.Core.Uint256.ofNat lhs))
          (Verity.Core.Int256.ofUint256 (Verity.Core.Uint256.ofNat rhs))).toUint256.val
    | .sar a b => do
        let lhs ← evalExprWithHelpers spec fields fuel state a
        let rhs ← evalExprWithHelpers spec fields fuel state b
        pure (Verity.Core.Int256.sar
          (Verity.Core.Int256.ofUint256 (Verity.Core.Uint256.ofNat lhs))
          (Verity.Core.Int256.ofUint256 (Verity.Core.Uint256.ofNat rhs))).toUint256.val
    | .byte a b => do
        let index ← evalExprWithHelpers spec fields fuel state a
        let value ← evalExprWithHelpers spec fields fuel state b
        pure (Verity.Core.Uint256.byte
          (Verity.Core.Uint256.ofNat index)
          (Verity.Core.Uint256.ofNat value)).val
    | .signextend a b => do
        let byteIdx ← evalExprWithHelpers spec fields fuel state a
        let value ← evalExprWithHelpers spec fields fuel state b
        pure (Verity.Core.Uint256.signextend
          (Verity.Core.Uint256.ofNat byteIdx)
          (Verity.Core.Uint256.ofNat value)).val
    | .mapping field key => do
        let keyVal ← evalExprWithHelpers spec fields fuel state key
        match findFieldWithResolvedSlot fields field with
        | some (field, slot) =>
            some (readFieldWord state.world field (Compiler.Proofs.abstractMappingSlot slot keyVal)).val
        | none => none
    | .mappingWord field key wordOffset => do
        let keyVal ← evalExprWithHelpers spec fields fuel state key
        match findFieldWithResolvedSlot fields field with
        | some (field, slot) =>
            some (readFieldWord state.world field
              (wordNormalize (Compiler.Proofs.abstractMappingSlot slot keyVal + wordOffset))).val
        | none => none
    | .mappingUint field key => do
        let keyVal ← evalExprWithHelpers spec fields fuel state key
        match findFieldWithResolvedSlot fields field with
        | some (field, slot) =>
            some (readFieldWord state.world field (Compiler.Proofs.abstractMappingSlot slot keyVal)).val
        | none => none
    | .mapping2 field key1 key2 => do
        let key1Val ← evalExprWithHelpers spec fields fuel state key1
        let key2Val ← evalExprWithHelpers spec fields fuel state key2
        match findFieldWithResolvedSlot fields field with
        | some (field, slot) =>
            let innerSlot := Compiler.Proofs.abstractMappingSlot slot key1Val
            some (readFieldWord state.world field (Compiler.Proofs.abstractMappingSlot innerSlot key2Val)).val
        | none => none
    | .mapping2Word field key1 key2 wordOffset => do
        let key1Val ← evalExprWithHelpers spec fields fuel state key1
        let key2Val ← evalExprWithHelpers spec fields fuel state key2
        match findFieldWithResolvedSlot fields field with
        | some (field, slot) =>
            let innerSlot := Compiler.Proofs.abstractMappingSlot slot key1Val
            let outerSlot := Compiler.Proofs.abstractMappingSlot innerSlot key2Val
            some (readFieldWord state.world field (wordNormalize (outerSlot + wordOffset))).val
        | none => none
    | .mappingPackedWord field key wordOffset packed => do
        let keyVal ← evalExprWithHelpers spec fields fuel state key
        match findFieldWithResolvedSlot fields field with
        | some (fieldInfo, slot) =>
            let targetSlot := wordNormalize
              (Compiler.Proofs.abstractMappingSlot slot keyVal + wordOffset)
            let rawWord := (readFieldWord state.world fieldInfo targetSlot).val
            some (Verity.Core.Uint256.and
              (Verity.Core.Uint256.shr packed.offset rawWord)
              (packedMaskNat packed)).val
        | none => none
    | .structMember field key memberName => do
        let keyVal ← evalExprWithHelpers spec fields fuel state key
        match findFieldWithResolvedSlot fields field, findStructMembers fields field with
        | some (fieldInfo, slot), some members =>
            match findStructMember members memberName with
            | some member =>
                let targetSlot := wordNormalize
                  (Compiler.Proofs.abstractMappingSlot slot keyVal + member.wordOffset)
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
        let key1Val ← evalExprWithHelpers spec fields fuel state key1
        let key2Val ← evalExprWithHelpers spec fields fuel state key2
        match findFieldWithResolvedSlot fields field, findStructMembers fields field with
        | some (fieldInfo, slot), some members =>
            match findStructMember members memberName with
            | some member =>
                let innerSlot := Compiler.Proofs.abstractMappingSlot slot key1Val
                let outerSlot := Compiler.Proofs.abstractMappingSlot innerSlot key2Val
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
    | .internalCall calleeName args =>
        match fuel with
        | 0 => none
        | fuel + 1 => do
            let argVals ← evalExprListWithHelpers spec fields (fuel + 1) state args
            let callee ← findUniqueInternalFunction? spec calleeName
            let hresult := interpretInternalFunctionFuel spec fuel callee state.world argVals
            if hresult.success then hresult.returnValue else none
    | .mload offset => do
        let resolvedOffset ← evalExprWithHelpers spec fields fuel state offset
        some (state.world.memory resolvedOffset).val
    | .tload offset => do
        let resolvedOffset ← evalExprWithHelpers spec fields fuel state offset
        some (state.world.transientStorage resolvedOffset).val
    | .calldataload offset => do
        let resolvedOffset ← evalExprWithHelpers spec fields fuel state offset
        some (Compiler.Proofs.YulGeneration.calldataloadWord state.selector state.world.calldata resolvedOffset)
    | .extcodesize addr => do
        let resolvedAddr ← evalExprWithHelpers spec fields fuel state addr
        some (state.world.codeSize (resolvedAddr % addressModulus)).val
    | .keccak256 offExpr sizeExpr => do
        -- Keep this in sync with the helper/call surface scans, which recurse
        -- into the offset and size expressions.
        let off ← evalExprWithHelpers spec fields fuel state offExpr
        let size ← evalExprWithHelpers spec fields fuel state sizeExpr
        some (keccakMemorySlice state.world.memory off size)
    | .memoryArrayLength name =>
        lookupBinding? state.bindings s!"{name}_length"
    | .memoryArrayElement name index => do
        let idx ← evalExprWithHelpers spec fields fuel state index
        let (dataOffset, length) ← dynamicArrayBinding? state.bindings name
        if idx < length then
          some (state.world.memory (wordNormalize (dataOffset + 32 * idx))).val
        else
          none
    | .arrayLength name =>
        lookupBinding? state.bindings s!"{name}_length"
    | .arrayElement name index => do
        let idx ← evalExprWithHelpers spec fields fuel state index
        let (dataOffset, length) ← dynamicArrayBinding? state.bindings name
        arrayElement? state.selector state.world.calldata dataOffset length idx
    | .dynamicBytesEq lhsName rhsName => do
        let (lhsOffset, lhsLength) ← dynamicArrayBinding? state.bindings lhsName
        let (rhsOffset, rhsLength) ← dynamicArrayBinding? state.bindings rhsName
        some (boolWord (DynamicAbi.dynamicBytesEqCalldata
          state.selector state.world.calldata
          lhsOffset lhsLength rhsOffset rhsLength))
    | .arrayElementDynamicWord name index wordOffset => do
        let idx ← evalExprWithHelpers spec fields fuel state index
        let (dataOffset, length) ← dynamicArrayBinding? state.bindings name
        arrayElementDynamicWord?
          state.selector state.world.calldata dataOffset length idx wordOffset
    | .arrayElementDynamicDataOffset name index => do
        let idx ← evalExprWithHelpers spec fields fuel state index
        let (dataOffset, length) ← dynamicArrayBinding? state.bindings name
        arrayElementDynamicHeadOffset?
          state.selector state.world.calldata dataOffset length idx
    | .arrayElementDynamicMemberLength name index wordOffset => do
        let idx ← evalExprWithHelpers spec fields fuel state index
        let (dataOffset, length) ← dynamicArrayBinding? state.bindings name
        arrayElementDynamicMemberLength?
          state.selector state.world.calldata dataOffset length idx wordOffset
    | .arrayElementDynamicMemberDataOffset name index wordOffset => do
        let idx ← evalExprWithHelpers spec fields fuel state index
        let (dataOffset, length) ← dynamicArrayBinding? state.bindings name
        arrayElementDynamicMemberDataOffset?
          state.selector state.world.calldata dataOffset length idx wordOffset
    | .arrayElementDynamicMemberElement name index wordOffset innerIndex => do
        let idx ← evalExprWithHelpers spec fields fuel state index
        let innerIdx ← evalExprWithHelpers spec fields fuel state innerIndex
        let (dataOffset, length) ← dynamicArrayBinding? state.bindings name
        arrayElementDynamicMemberElement?
          state.selector state.world.calldata dataOffset length idx wordOffset innerIdx
    -- Unmodeled / codegen-only constructors (no helper-aware semantics yet).
    -- Listed explicitly rather than via `| _ => none` so the
    -- `_mutual.eq_def` deriver does not enumerate the complement and trip
    -- the 200 000-heartbeat ceiling whenever a new `Expr` constructor
    -- lands (verity#1842).
    | .returndataOptionalBoolAt offset => do
        let resolvedOffset ← evalExprWithHelpers spec fields fuel state offset
        some (state.world.returndataOptionalBool resolvedOffset)
    -- The reserved `exp` builtin lane: pure arithmetic wearing an
    -- `externalCall` node, so it needs no helper environment. Like the plain
    -- evaluator it reduces modulo 2^256 at every step so full-domain uint256
    -- exponents stay executable.
    | .externalCall name [base, exponent] =>
        if name == builtinExpName then do
          let baseVal ← evalExprWithHelpers spec fields fuel state base
          let exponentVal ← evalExprWithHelpers spec fields fuel state exponent
          pure (Verity.Core.Uint256.powEff
            (Verity.Core.Uint256.ofNat baseVal)
            (Verity.Core.Uint256.ofNat exponentVal)).val
        else none
    | .mulDiv512Down _ _ _ | .mulDiv512Up _ _ _
    | .paramDynamicHeadWord _ _ | .paramDynamicStaticComposite _ _
    | .paramDynamicMemberLength _ _
    | .paramDynamicMemberDataOffset _ _ | .paramDynamicMemberElement _ _ _
    | .arrayElementWord _ _ _ _
    | .call _ _ _ _ _ _ _ | .staticcall _ _ _ _ _ _ | .delegatecall _ _ _ _ _ _
    | .externalCall _ _ | .mappingChain _ _ | .intrinsic _ _ _ _
    | .forkIfAtLeast _ _ _
    | .adtConstruct _ _ _ | .adtTag _ _ | .adtField _ _ _ _ _ => none
  termination_by expr => (fuel, sizeOf expr)
  decreasing_by all_goals (simp_wf; omega)
  def evalExprListWithHelpers
      (spec : CompilationModel)
      (fields : List Field)
      (fuel : Nat)
      (state : RuntimeState) : List Expr → Option (List Nat)
    | [] => some []
    | expr :: rest => do
        let value ← evalExprWithHelpers spec fields fuel state expr
        let values ← evalExprListWithHelpers spec fields fuel state rest
        pure (value :: values)
  termination_by exprs => (fuel, sizeOf exprs)
  decreasing_by all_goals (simp_wf; omega)
  def execStmtWithHelpers
      (spec : CompilationModel)
      (fields : List Field)
      (fuel : Nat)
      (state : RuntimeState) : Stmt → StmtResult
    | .letVar name value =>
        match evalExprWithHelpers spec fields fuel state value with
        | some resolved =>
            .continue { state with bindings := bindValue state.bindings name resolved }
        | none => .revert
    | .assignVar name value =>
        match evalExprWithHelpers spec fields fuel state value with
        | some resolved =>
            .continue { state with bindings := bindValue state.bindings name resolved }
        | none => .revert
    | .setStorage fieldName value =>
        match findFieldWriteSlots fields fieldName, evalExprWithHelpers spec fields fuel state value with
        | some slots, some resolved =>
            .continue { state with world := writeUintFieldSlots fields fieldName state.world slots resolved }
        | _, _ => .revert
    | .setStorageWord fieldName wordOffset value =>
        match findFieldWriteSlots fields fieldName,
            evalExprWithHelpers spec fields fuel state value with
        | some slots, some resolved =>
            .continue
              { state with
                  world := writeStorageWordFieldSlots fields fieldName state.world slots wordOffset resolved }
        | _, _ => .revert
    | .setMapping fieldName key value =>
        match findFieldWriteSlots fields fieldName,
            evalExprWithHelpers spec fields fuel state key,
            evalExprWithHelpers spec fields fuel state value with
        | some slots@(_ :: _), some resolvedKey, some resolved =>
            .continue
              { state with
                  world := writeAddressKeyedMappingFieldSlots
                    fields fieldName state.world slots resolvedKey resolved }
        | _, _, _ => .revert
    | .setMappingWord fieldName key wordOffset value =>
        match findFieldWriteSlots fields fieldName,
            evalExprWithHelpers spec fields fuel state key,
            evalExprWithHelpers spec fields fuel state value with
        | some slots@(_ :: _), some resolvedKey, some resolved =>
            .continue
               { state with
                   world := writeAddressKeyedMappingWordFieldSlots
                     fields fieldName state.world slots resolvedKey wordOffset resolved }
        | _, _, _ => .revert
    | .setMappingPackedWord fieldName key wordOffset packed value =>
        match findFieldWriteSlots fields fieldName,
            evalExprWithHelpers spec fields fuel state key,
            evalExprWithHelpers spec fields fuel state value with
        | some slots@(_ :: _), some resolvedKey, some resolved =>
            if packedBitsValid packed then
              .continue
                { state with
                    world := writeAddressKeyedMappingPackedWordFieldSlots
                      fields fieldName state.world slots resolvedKey wordOffset packed resolved }
            else
              .revert
        | _, _, _ => .revert
    | .setStructMember fieldName key memberName value =>
        match findFieldWriteSlots fields fieldName,
            findStructMembers fields fieldName,
            evalExprWithHelpers spec fields fuel state key,
            evalExprWithHelpers spec fields fuel state value with
        | some slots@(_ :: _), some members, some resolvedKey, some resolved =>
            match findStructMember members memberName with
            | some { wordOffset := wordOffset, packed := none, .. } =>
                .continue
                  { state with
                      world := writeAddressKeyedMappingWordFieldSlots
                        fields fieldName state.world slots resolvedKey wordOffset resolved }
            | some { wordOffset := wordOffset, packed := some packed, .. } =>
                if packedBitsValid packed then
                  .continue
                    { state with
                        world := writeAddressKeyedMappingPackedWordFieldSlots
                          fields fieldName state.world slots resolvedKey wordOffset packed resolved }
                else
                  .revert
            | _ => .revert
        | _, _, _, _ => .revert
    | .setMapping2 fieldName key1 key2 value =>
        match findFieldWriteSlots fields fieldName,
            evalExprWithHelpers spec fields fuel state key1,
            evalExprWithHelpers spec fields fuel state key2,
            evalExprWithHelpers spec fields fuel state value with
        | some slots@(_ :: _), some resolvedKey1, some resolvedKey2, some resolved =>
            .continue
              { state with
                  world :=
                    writeAddressKeyedMapping2FieldSlots
                      fields fieldName state.world slots resolvedKey1 resolvedKey2 resolved }
        | _, _, _, _ => .revert
    | .setMapping2Word fieldName key1 key2 wordOffset value =>
        match findFieldWriteSlots fields fieldName,
            evalExprWithHelpers spec fields fuel state key1,
            evalExprWithHelpers spec fields fuel state key2,
            evalExprWithHelpers spec fields fuel state value with
        | some slots@(_ :: _), some resolvedKey1, some resolvedKey2, some resolved =>
            .continue
              { state with
                  world :=
                    writeAddressKeyedMapping2WordFieldSlots
                      fields
                      fieldName
                      state.world
                      slots
                      resolvedKey1
                      resolvedKey2
                      wordOffset
                      resolved }
        | _, _, _, _ => .revert
    | .setStructMember2 fieldName key1 key2 memberName value =>
        match findFieldWriteSlots fields fieldName,
            findStructMembers fields fieldName,
            evalExprWithHelpers spec fields fuel state key1,
            evalExprWithHelpers spec fields fuel state key2,
            evalExprWithHelpers spec fields fuel state value with
        | some slots@(_ :: _), some members, some resolvedKey1, some resolvedKey2, some resolved =>
            match findStructMember members memberName with
            | some { wordOffset := wordOffset, packed := none, .. } =>
                .continue
                  { state with
                      world := writeAddressKeyedMapping2WordFieldSlots
                        fields fieldName state.world slots resolvedKey1 resolvedKey2 wordOffset resolved }
            | some { wordOffset := wordOffset, packed := some packed, .. } =>
                if packedBitsValid packed then
                  .continue
                    { state with
                        world := writeAddressKeyedMapping2PackedWordFieldSlots
                          fields fieldName state.world slots resolvedKey1 resolvedKey2 wordOffset packed resolved }
                else
                  .revert
            | _ => .revert
        | _, _, _, _, _ => .revert
    | .setMappingUint fieldName key value =>
        match findFieldWriteSlots fields fieldName,
            evalExprWithHelpers spec fields fuel state key,
            evalExprWithHelpers spec fields fuel state value with
        | some slots@(_ :: _), some resolvedKey, some resolved =>
            .continue
              { state with
                  world := writeUintKeyedMappingFieldSlots
                    fields fieldName state.world slots resolvedKey resolved }
        | _, _, _ => .revert
    | .setMappingChain fieldName keys value =>
        match findFieldWriteSlots fields fieldName,
            evalExprListWithHelpers spec fields fuel state keys,
            evalExprWithHelpers spec fields fuel state value with
        | some slots@(_ :: _), some resolvedKeys, some resolved =>
            .continue
              { state with
                  world := writeAddressKeyedMappingChainFieldSlots
                    fields fieldName state.world slots resolvedKeys resolved }
        | _, _, _ => .revert
    | .storageArrayPush fieldName value =>
        match findFieldWithResolvedSlot fields fieldName, evalExprWithHelpers spec fields fuel state value with
        | some ({ ty := .dynamicArray _, .. }, slot), some resolved =>
            let updated := state.world.storageArray slot ++ [(resolved : Verity.Core.Uint256)]
            .continue { state with world := writeStorageArray state.world slot updated }
        | _, _ => .revert
    | .storageArrayPop fieldName =>
        match findFieldWithResolvedSlot fields fieldName with
        | some ({ ty := .dynamicArray _, .. }, slot) =>
            match storageArrayDropLast? (state.world.storageArray slot) with
            | some updated =>
                .continue { state with world := writeStorageArray state.world slot updated }
            | none => .revert
        | _ => .revert
    | .setStorageArrayElement fieldName index value =>
        match findFieldWithResolvedSlot fields fieldName,
            evalExprWithHelpers spec fields fuel state index,
            evalExprWithHelpers spec fields fuel state value with
        | some ({ ty := .dynamicArray _, .. }, slot), some idx, some resolved =>
            match storageArraySetAt (state.world.storageArray slot) idx resolved with
            | some updated =>
                .continue { state with world := writeStorageArray state.world slot updated }
            | none => .revert
        | some ({ ty := .fixedArrayUint128 size, .. }, _), some idx, some resolved =>
            match findFieldWriteSlots fields fieldName >>= fun slots =>
                writeFixedUint128ArrayElementSlots state.world slots size idx resolved with
            | some world => .continue { state with world := world }
            | none => .revert
        | _, _, _ => .revert
    | .setStorageAddr fieldName value =>
        match findFieldWriteSlots fields fieldName, evalExprWithHelpers spec fields fuel state value with
        | some slots, some resolved =>
            .continue { state with world := writeAddressFieldSlots fields fieldName state.world slots resolved }
        | _, _ => .revert
    | .setImmutable name value =>
        match evalExprWithHelpers spec fields fuel state value with
        | some resolved =>
            .continue
              { state with
                  immutable := fun immName =>
                    if immName == name then resolved else state.immutable immName }
        | none => .revert
    | .mstore offset value =>
        match evalExprWithHelpers spec fields fuel state offset,
            evalExprWithHelpers spec fields fuel state value with
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
    | .tstore offset value =>
        match evalExprWithHelpers spec fields fuel state offset,
            evalExprWithHelpers spec fields fuel state value with
        | some resolvedOffset, some resolvedValue =>
            let resolvedOffset := wordNormalize resolvedOffset
            .continue {
              state with
              world := state.world.writeTransient resolvedOffset resolvedValue
            }
        | _, _ => .revert
    | .calldatacopy destOffset sourceOffset size =>
        match evalExprWithHelpers spec fields fuel state destOffset,
            evalExprWithHelpers spec fields fuel state sourceOffset,
            evalExprWithHelpers spec fields fuel state size with
        | some dst, some src, some sz =>
            .continue {
              state with
              world := {
                state.world with
                memory := fun o =>
                  if Compiler.Proofs.YulGeneration.calldatacopyWritesAt dst sz o then
                    Verity.Core.Uint256.ofNat
                      (Compiler.Proofs.YulGeneration.calldataloadWord
                        state.selector state.world.calldata (src + (o - dst)))
                  else state.world.memory o
              }
            }
        | _, _, _ => .revert
    | .returndataCopy destOffset sourceOffset size =>
        match evalExprWithHelpers spec fields fuel state destOffset,
            evalExprWithHelpers spec fields fuel state sourceOffset,
            evalExprWithHelpers spec fields fuel state size with
        | some _, some src, some sz =>
            if src + sz = 0 then .continue state else .revert
        | _, _, _ => .revert
    | .require cond _ =>
        match evalExprWithHelpers spec fields fuel state cond with
        | some resolved =>
            if resolved != 0 then .continue state else .revert
        | none => .revert
    | .requireError cond _ args =>
        match evalExprWithHelpers spec fields fuel state cond with
        | some resolved =>
            if resolved != 0 then .continue state else typedErrorRevertResult fields state args
        | none => .revert
    | .revertError _ args =>
        typedErrorRevertResult fields state args
    | .return value =>
        match evalExprWithHelpers spec fields fuel state value with
        | some resolved => .return resolved
            { state with
                world := { state.world with
                  memory := fun o => if o = 0 then resolved else state.world.memory o } }
        | none => .revert
    | .stop => .stop state
    | .ite cond thenBranch elseBranch =>
        match evalExprWithHelpers spec fields fuel state cond with
        | some resolved =>
            if resolved != 0 then
              execStmtListWithHelpers spec fields fuel state thenBranch
            else
              execStmtListWithHelpers spec fields fuel state elseBranch
        | none => .revert
    | .internalCall calleeName args =>
        match fuel with
        | 0 => .revert
        | fuel + 1 =>
            match evalExprListWithHelpers spec fields (fuel + 1) state args,
                findUniqueInternalFunction? spec calleeName with
            | some argVals, some callee =>
                let hresult := interpretInternalFunctionFuel spec fuel callee state.world argVals
                if hresult.success then
                  .continue { state with world := hresult.world }
                else
                  .revert
            | _, _ => .revert
    | .internalCallAssign names calleeName args =>
        match fuel with
        | 0 => .revert
        | fuel + 1 =>
            match evalExprListWithHelpers spec fields (fuel + 1) state args,
                findUniqueInternalFunction? spec calleeName with
            | some argVals, some callee =>
                let hresult := interpretInternalFunctionFuel spec fuel callee state.world argVals
                if hresult.success then
                  match names, hresult.returnValue with
                  | [name], some value =>
                      .continue { state with
                        world := hresult.world
                        bindings := bindValue state.bindings name value
                      }
                  | _, _ => .revert
                else
                  .revert
            | _, _ => .revert
    | .emit eventName args =>
        match evalExprListWithHelpers spec fields fuel state args with
        | some resolved =>
            match eventFromResolvedArgs? spec.events eventName resolved,
                eventScratchMemoryAfterEmit? spec.events eventName resolved state.world.memory with
            | some event, some memory =>
                .continue { state with
                  world := {
                    state.world with
                    memory := memory
                    events := state.world.events ++ [event] } }
            | _, _ => .revert
        | none => .revert
    | .forEach varName count body =>
        match evalExprWithHelpers spec fields fuel state count with
        | some bound =>
            let initialLoopState :=
              { state with bindings := bindValue state.bindings varName (wordNormalize 0) }
            execForEachLoop varName
              (fun loopState => execStmtListWithHelpers spec fields fuel loopState body)
              initialLoopState 0 bound
        | none => .revert
    | .forEachSetBit varName bitmap body =>
        match evalExprWithHelpers spec fields fuel state bitmap with
        | some bits =>
            execForEachSetBitLoop varName
              (fun loopState => execStmtListWithHelpers spec fields fuel loopState body)
              256 state bits
        | none => .revert
    | .revertReturndata => .revert
    | .externalCallBind resultVars _externalName args =>
        match evalExprListWithHelpers spec fields fuel state args with
        | some _ =>
            let outcome := state.externalCallOracle state.externalCallIndex
            if outcome.succeeded then
              if outcome.returnValues.length != resultVars.length then .revert
              else
                .continue
                  { state with
                      world := returndataAfterCall outcome
                        (outcome.postCallWorld.getD state.world)
                      bindings := bindValues state.bindings resultVars
                        (outcome.returnValues.map wordNormalize)
                      externalCallIndex := state.externalCallIndex + 1 }
            else .revert
        | none => .revert
    | .tryExternalCallBind successVar resultVars _externalName args =>
        match evalExprListWithHelpers spec fields fuel state args with
        | some _ =>
            let outcome := state.externalCallOracle state.externalCallIndex
            if outcome.succeeded then
              if outcome.returnValues.length != resultVars.length then .revert
              else
                .continue
                  { state with
                      world := returndataAfterCall outcome
                        (outcome.postCallWorld.getD state.world)
                      bindings := bindValues
                        (bindValue state.bindings successVar 1)
                        resultVars (outcome.returnValues.map wordNormalize)
                      externalCallIndex := state.externalCallIndex + 1 }
            else
              .continue
                { state with
                    world := returndataAfterCall outcome state.world
                    bindings := bindValues
                      (bindValue state.bindings successVar 0)
                      resultVars (outcome.returnValues.map wordNormalize)
                    externalCallIndex := state.externalCallIndex + 1 }
        | none => .revert
    | .ecm mod args =>
        match evalExprListWithHelpers spec fields fuel state args with
        | some _ =>
            let outcome := state.externalCallOracle state.externalCallIndex
            if outcome.succeeded then
              if outcome.returnValues.length != mod.resultVars.length then .revert
              else
                .continue
                  { state with
                      world := returndataAfterCall outcome
                        (mod.committedWorld outcome.postCallWorld state.world)
                      bindings := bindValues state.bindings mod.resultVars
                        (outcome.returnValues.map wordNormalize)
                      externalCallIndex := state.externalCallIndex + 1 }
            else .revert
        | none => .revert
    | _ => .revert
  termination_by stmt => (fuel, sizeOf stmt)
  decreasing_by all_goals (simp_wf; omega)
  def execStmtListWithHelpers
      (spec : CompilationModel)
      (fields : List Field)
      (fuel : Nat)
      (state : RuntimeState) : List Stmt → StmtResult
    | [] => .continue state
    | stmt :: rest =>
        match execStmtWithHelpers spec fields fuel state stmt with
        | .continue next => execStmtListWithHelpers spec fields fuel next rest
        | .stop next => .stop next
        | .return value next => .return value next
        | .revert => .revert
  termination_by stmts => (fuel, sizeOf stmts)
  decreasing_by all_goals (simp_wf; omega)
  def interpretInternalFunctionFuel
      (spec : CompilationModel)
      (fuel : Nat)
      (fn : FunctionSpec)
      (initialWorld : Verity.ContractState)
      (args : List Nat)
      (externalCallOracle : Nat → ExternalCallOutcome := fun _ => ⟨false, [], none⟩)
      (externalCallIndex : Nat := 0) : InternalFunctionResult :=
    let fields := effectiveFields spec
    match bindInternalArgs fn.params args with
    | none => revertedInternalResult initialWorld
    | some bindings =>
        match execStmtListWithHelpers spec fields fuel
            { world := initialWorld, bindings := bindings,
              externalCallOracle := externalCallOracle,
              externalCallIndex := externalCallIndex } fn.body with
        | .continue state => successInternalResult state.world none
        | .stop state => successInternalResult state.world none
        | .return value state => successInternalResult state.world (some value)
        | .revert => revertedInternalResult initialWorld
  termination_by (fuel, sizeOf fn.body + 1)
  decreasing_by all_goals (simp_wf; omega)
end

theorem evalExprListWithHelpers_length_of_some
    {spec : CompilationModel}
    {fields : List Field}
    {fuel : Nat}
    {state : RuntimeState}
    {exprs : List Expr}
    {values : List Nat}
    (heval : evalExprListWithHelpers spec fields fuel state exprs = some values) :
    values.length = exprs.length := by
  induction exprs generalizing values with
  | nil =>
      simp [evalExprListWithHelpers] at heval
      cases heval
      rfl
  | cons expr rest ih =>
      cases hhead : evalExprWithHelpers spec fields fuel state expr <;>
        simp [evalExprListWithHelpers, hhead] at heval
      cases htail : evalExprListWithHelpers spec fields fuel state rest <;>
        simp [htail] at heval
      cases heval
      simp [ih htail]

theorem execStmtWithHelpers_emit_supported_continues
    {spec : CompilationModel}
    {fields : List Field}
    {fuel : Nat}
    {state : RuntimeState}
    {eventName : String}
    {args : List Expr}
    {values : List Nat}
    (heval : evalExprListWithHelpers spec fields fuel state args = some values)
    (hsupport : eventEmissionProofSupported spec.events eventName args = true) :
    ∃ event memory,
      eventFromResolvedArgs? spec.events eventName values = some event ∧
      eventScratchMemoryAfterEmit? spec.events eventName values state.world.memory = some memory ∧
      execStmtWithHelpers spec fields fuel state (.emit eventName args) =
        .continue { state with
          world := {
            state.world with
            memory := memory
            events := state.world.events ++ [event] } } := by
  have hlen : values.length = args.length :=
    evalExprListWithHelpers_length_of_some heval
  rcases exists_eventFromResolvedArgs?_of_supported_length hsupport hlen with
    ⟨event, hevent⟩
  rcases exists_eventScratchMemoryAfterEmit?_of_supported_length hsupport hlen with
    ⟨memory, hmemory⟩
  exact ⟨event, memory, hevent, hmemory, by
    simp [execStmtWithHelpers, heval, hevent, hmemory]⟩

@[simp] theorem interpretInternalFunctionFuel_zero
    (spec : CompilationModel)
    (fn : FunctionSpec)
    (initialWorld : Verity.ContractState)
    (args : List Nat) :
    interpretInternalFunctionFuel spec 0 fn initialWorld args =
      let fields := effectiveFields spec
      match bindInternalArgs fn.params args with
      | none => revertedInternalResult initialWorld
      | some bindings =>
          match execStmtListWithHelpers spec fields 0
              { world := initialWorld, bindings := bindings } fn.body with
          | .continue state => successInternalResult state.world none
          | .stop state => successInternalResult state.world none
          | .return value state => successInternalResult state.world (some value)
          | .revert => revertedInternalResult initialWorld := by
  simp [interpretInternalFunctionFuel]

theorem interpretInternalFunctionFuel_succ
    (spec : CompilationModel)
    (fuel : Nat)
    (fn : FunctionSpec)
    (initialWorld : Verity.ContractState)
    (args : List Nat) :
    interpretInternalFunctionFuel spec (fuel + 1) fn initialWorld args =
      let fields := effectiveFields spec
      match bindInternalArgs fn.params args with
      | none => revertedInternalResult initialWorld
      | some bindings =>
          match execStmtListWithHelpers spec fields (fuel + 1)
              { world := initialWorld, bindings := bindings } fn.body with
          | .continue state => successInternalResult state.world none
          | .stop state => successInternalResult state.world none
          | .return value state => successInternalResult state.world (some value)
          | .revert => revertedInternalResult initialWorld := by
  simp [interpretInternalFunctionFuel]

/-- Semantic contract attached to an internal-helper summary witness. The summary
is intentionally phrased against the helper-aware source semantics so later
Layer 2 composition lemmas can consume it without changing theorem targets. -/
def InternalHelperSummarySound
    (spec : CompilationModel)
    (fn : FunctionSpec)
    (summary : InternalHelperSummaryContract) : Prop :=
  ∀ fuel initialWorld args,
    let result := interpretInternalFunctionFuel spec fuel fn initialWorld args
    summary.post fuel 0 initialWorld args result.success result.returnValue result.world

/-- The direct-callee summary inventory carried by `SupportedBodyHelperInterface`
becomes a proof interface once each summary contract is proved sound for the
actual helper-aware source semantics. -/
def SupportedBodyHelperSummariesSound
    (spec : CompilationModel)
    (fn : FunctionSpec)
    (hHelpers : SupportedBodyHelperInterface spec fn) : Prop :=
  ∀ calleeName (hmem : calleeName ∈ helperCallNames fn),
    InternalHelperSummarySound spec
      (hHelpers.summaryOfCall hmem).callee
      (hHelpers.summaryContractOfCall hmem)

def interpretFunctionWithHelpers
    (spec : CompilationModel)
    (fuel : Nat)
    (fn : FunctionSpec)
    (tx : IRTransaction)
    (initialWorld : Verity.ContractState)
    (externalCallOracle : Nat → ExternalCallOutcome := fun _ => ⟨false, [], none⟩) :
    SourceContractResult :=
  let worldWithTx := withTransactionContext initialWorld tx
  let fields := effectiveFields spec
  match bindExternalParams tx.functionSelector fn.params tx.args with
  | none => revertedResult spec worldWithTx
  | some bindings =>
      match execStmtListWithHelpers spec fields fuel
          { world := worldWithTx, bindings := bindings, selector := tx.functionSelector,
            externalCallOracle := externalCallOracle } fn.body with
      | .continue state => successResult spec state.world none
      | .stop state => successResult spec state.world none
      | .return value state => successResult spec state.world (some value)
      | .revert => revertedResult spec worldWithTx

def interpretConstructorWithHelpers
    (spec : CompilationModel)
    (fuel : Nat)
    (ctor : ConstructorSpec)
    (tx : IRTransaction)
    (initialWorld : Verity.ContractState)
    (externalCallOracle : Nat → ExternalCallOutcome := fun _ => ⟨false, [], none⟩) :
    SourceContractResult :=
  let constructorWorldWithTx := withTransactionContext initialWorld tx
  let fields := effectiveFields spec
  if constructorTouchesUnsupportedRawCalldataSurface spec ctor then
    revertedResult spec constructorWorldWithTx
  else
    match constructorExecutionBindings ctor tx.args with
    | none => revertedResult spec constructorWorldWithTx
    | some bindings =>
        match execStmtListWithHelpers spec fields fuel
            { world := constructorWorldWithTx, bindings := bindings,
              selector := tx.functionSelector,
              externalCallOracle := externalCallOracle }
            ctor.body with
        | .continue state => successResult spec state.world none
        | .stop state => successResult spec state.world none
        | .return value state => successResult spec state.world (some value)
        | .revert => revertedResult spec constructorWorldWithTx

def interpretContractWithHelpers
    (spec : CompilationModel)
    (selectors : List Nat)
    (fuel : Nat)
    (tx : IRTransaction)
    (initialWorld : Verity.ContractState)
    (externalCallOracle : Nat → ExternalCallOutcome := fun _ => ⟨false, [], none⟩) :
    SourceContractResult :=
  match findFunctionBySelector spec selectors tx.functionSelector with
  | some fn =>
      if !fn.isPayable && tx.msgValue % Compiler.Constants.evmModulus != 0 then
        revertedResult spec (withTransactionContext initialWorld tx)
      else
        interpretFunctionWithHelpers spec fuel fn tx initialWorld externalCallOracle
  | none => revertedResult spec (withTransactionContext initialWorld tx)

theorem helperSummarySound
    {spec : CompilationModel}
    {fn : FunctionSpec}
    {summary : InternalHelperSummaryContract}
    (hsound : InternalHelperSummarySound spec fn summary)
    (fuel : Nat)
    (initialWorld : Verity.ContractState)
    (args : List Nat) :
    let result := interpretInternalFunctionFuel spec fuel fn initialWorld args
    summary.post fuel 0 initialWorld args result.success result.returnValue result.world :=
  hsound fuel initialWorld args

/-- Concrete source helper-body `.continue` case for `InternalHelperSummarySound`.
This exposes the `interpretInternalFunctionFuel` reduction and then consumes the
real summary postcondition. -/
theorem InternalHelperSummarySound.post_of_execStmtListWithHelpers_continue
    {spec : CompilationModel}
    {fn : FunctionSpec}
    {summary : InternalHelperSummaryContract}
    (hsound : InternalHelperSummarySound spec fn summary)
    {fuel : Nat}
    {initialWorld : Verity.ContractState}
    {args : List Nat}
    {bindings : List (String × Nat)}
    {finalState : RuntimeState}
    (hbind : bindInternalArgs fn.params args = some bindings)
    (hbody :
      execStmtListWithHelpers spec (effectiveFields spec) fuel
        { world := initialWorld, bindings := bindings } fn.body =
          .continue finalState) :
    interpretInternalFunctionFuel spec fuel fn initialWorld args =
        successInternalResult finalState.world none ∧
      summary.post fuel 0 initialWorld args true none finalState.world := by
  have hinterp :
      interpretInternalFunctionFuel spec fuel fn initialWorld args =
        successInternalResult finalState.world none := by
    simp [interpretInternalFunctionFuel, hbind, hbody]
  have hpost := hsound fuel initialWorld args
  refine ⟨hinterp, ?_⟩
  simpa [hinterp, successInternalResult] using hpost

/-- Concrete source helper-body `.return` case for `InternalHelperSummarySound`.
This is the source-side counterpart of singleton helper-return result cases on
the compiled side. -/
theorem InternalHelperSummarySound.post_of_execStmtListWithHelpers_return
    {spec : CompilationModel}
    {fn : FunctionSpec}
    {summary : InternalHelperSummaryContract}
    (hsound : InternalHelperSummarySound spec fn summary)
    {fuel : Nat}
    {initialWorld : Verity.ContractState}
    {args : List Nat}
    {bindings : List (String × Nat)}
    {value : Nat}
    {finalState : RuntimeState}
    (hbind : bindInternalArgs fn.params args = some bindings)
    (hbody :
      execStmtListWithHelpers spec (effectiveFields spec) fuel
        { world := initialWorld, bindings := bindings } fn.body =
          .return value finalState) :
    interpretInternalFunctionFuel spec fuel fn initialWorld args =
        successInternalResult finalState.world (some value) ∧
      summary.post fuel 0 initialWorld args true (some value) finalState.world := by
  have hinterp :
      interpretInternalFunctionFuel spec fuel fn initialWorld args =
        successInternalResult finalState.world (some value) := by
    simp [interpretInternalFunctionFuel, hbind, hbody]
  have hpost := hsound fuel initialWorld args
  refine ⟨hinterp, ?_⟩
  simpa [hinterp, successInternalResult] using hpost

/-- Concrete source helper-body `.stop` case for `InternalHelperSummarySound`.
Source internal-helper interpretation records this as a successful `none`
result; the compiled-side runtime still propagates `.stop`, so full N1a needs a
separate stop-exclusion hypothesis before this case can be ruled out. -/
theorem InternalHelperSummarySound.post_of_execStmtListWithHelpers_stop
    {spec : CompilationModel}
    {fn : FunctionSpec}
    {summary : InternalHelperSummaryContract}
    (hsound : InternalHelperSummarySound spec fn summary)
    {fuel : Nat}
    {initialWorld : Verity.ContractState}
    {args : List Nat}
    {bindings : List (String × Nat)}
    {finalState : RuntimeState}
    (hbind : bindInternalArgs fn.params args = some bindings)
    (hbody :
      execStmtListWithHelpers spec (effectiveFields spec) fuel
        { world := initialWorld, bindings := bindings } fn.body =
          .stop finalState) :
    interpretInternalFunctionFuel spec fuel fn initialWorld args =
        successInternalResult finalState.world none ∧
      summary.post fuel 0 initialWorld args true none finalState.world := by
  have hinterp :
      interpretInternalFunctionFuel spec fuel fn initialWorld args =
        successInternalResult finalState.world none := by
    simp [interpretInternalFunctionFuel, hbind, hbody]
  have hpost := hsound fuel initialWorld args
  refine ⟨hinterp, ?_⟩
  simpa [hinterp, successInternalResult] using hpost

theorem helperSummaryPreservesWorldOnSuccess
    {summary : InternalHelperSummaryContract}
    (hpreserve : InternalHelperSummaryPreservesWorldOnSuccess summary)
    {fuel : Nat}
    {initialWorld : Verity.ContractState}
    {args : List Nat}
    {success : Bool}
    {returnValue : Option Nat}
    {finalWorld : Verity.ContractState}
    (hpost : summary.post fuel 0 initialWorld args success returnValue finalWorld)
    (hsuccess : success = true) :
    finalWorld = initialWorld :=
  hpreserve fuel 0 initialWorld args success returnValue finalWorld hpost hsuccess

theorem evalExprWithHelpers_internalCall_obeys_summary
    {spec : CompilationModel}
    {fields : List Field}
    {fuel : Nat}
    {state : RuntimeState}
    {calleeName : String}
    {args : List Expr}
    {callee : FunctionSpec}
    {summary : InternalHelperSummaryContract}
    (hfind : findUniqueInternalFunction? spec calleeName = some callee)
    (hsound : InternalHelperSummarySound spec callee summary)
    {argVals : List Nat}
    (hargs : evalExprListWithHelpers spec fields fuel state args = some argVals) :
    let result := interpretInternalFunctionFuel spec fuel callee state.world argVals
    summary.post fuel 0 state.world argVals result.success result.returnValue result.world := by
  simpa [InternalHelperSummarySound] using hsound fuel state.world argVals

theorem evalExprWithHelpers_internalCall_preserves_world
    {spec : CompilationModel}
    {fields : List Field}
    {fuel : Nat}
    {state : RuntimeState}
    {calleeName : String}
    {args : List Expr}
    {callee : FunctionSpec}
    {summary : InternalHelperSummaryContract}
    (hfind : findUniqueInternalFunction? spec calleeName = some callee)
    (hsound : InternalHelperSummarySound spec callee summary)
    (hpreserve : InternalHelperSummaryPreservesWorldOnSuccess summary)
    {argVals : List Nat}
    (hargs : evalExprListWithHelpers spec fields fuel state args = some argVals) :
    let result := interpretInternalFunctionFuel spec fuel callee state.world argVals
    result.success = true → result.world = state.world := by
  intro result hsuccess
  exact helperSummaryPreservesWorldOnSuccess hpreserve
    (hpost := evalExprWithHelpers_internalCall_obeys_summary
      (hfind := hfind) (hsound := hsound) (hargs := hargs))
    hsuccess

theorem execStmtWithHelpers_internalCall_obeys_summary
    {spec : CompilationModel}
    {fields : List Field}
    {fuel : Nat}
    {state : RuntimeState}
    {calleeName : String}
    {args : List Expr}
    {callee : FunctionSpec}
    {summary : InternalHelperSummaryContract}
    (hfind : findUniqueInternalFunction? spec calleeName = some callee)
    (hsound : InternalHelperSummarySound spec callee summary)
    {argVals : List Nat}
    (hargs : evalExprListWithHelpers spec fields fuel state args = some argVals) :
    let result := interpretInternalFunctionFuel spec fuel callee state.world argVals
    summary.post fuel 0 state.world argVals result.success result.returnValue result.world := by
  simpa [execStmtWithHelpers, hfind, hargs] using
    evalExprWithHelpers_internalCall_obeys_summary
      (hfind := hfind)
      (hsound := hsound)
      (hargs := hargs)

theorem execStmtWithHelpers_internalCallAssign_obeys_summary
    {spec : CompilationModel}
    {fields : List Field}
    {fuel : Nat}
    {state : RuntimeState}
    {names : List String}
    {calleeName : String}
    {args : List Expr}
    {callee : FunctionSpec}
    {summary : InternalHelperSummaryContract}
    (hfind : findUniqueInternalFunction? spec calleeName = some callee)
    (hsound : InternalHelperSummarySound spec callee summary)
    {argVals : List Nat}
    (hargs : evalExprListWithHelpers spec fields fuel state args = some argVals) :
    let result := interpretInternalFunctionFuel spec fuel callee state.world argVals
    summary.post fuel 0 state.world argVals result.success result.returnValue result.world := by
  simpa [execStmtWithHelpers, hfind, hargs] using
    evalExprWithHelpers_internalCall_obeys_summary
      (hfind := hfind)
      (hsound := hsound)
      (hargs := hargs)

/-- Bridge from `SupportedInternalHelperWitness` conditions to
`findUniqueInternalFunction?` success.  The uniqueness premise
(`(spec.functions.map (·.name)).Nodup`) ensures the filter in
`findUniqueInternalFunction?` produces exactly one match. -/
private theorem findUniqueInternalFunction?_of_witness
    {spec : CompilationModel}
    {calleeName : String}
    (witness : SupportedInternalHelperWitness spec calleeName)
    (hnodup : (spec.functions.map (·.name)).Nodup) :
    findUniqueInternalFunction? spec calleeName = some witness.callee := by
  unfold findUniqueInternalFunction?
  have hmem := witness.summary.present
  have hinternal := witness.summary.internal
  have hname := witness.nameEq
  -- Show that witness.callee passes the filter predicate
  have hpass : (fun fn => fn.isInternal && fn.name == calleeName) witness.callee = true := by
    simp [hinternal, hname, BEq.beq, decide_eq_true_eq]
  -- The filter contains witness.callee
  have hin_filter : witness.callee ∈ spec.functions.filter (fun fn => fn.isInternal && fn.name == calleeName) :=
    List.mem_filter.mpr ⟨hmem, hpass⟩
  -- Any element in the filter equals witness.callee (by name-nodup + name equality)
  have hfilter_eq : ∀ fn ∈ spec.functions.filter (fun fn => fn.isInternal && fn.name == calleeName),
      fn = witness.callee := by
    intro fn hfn
    have ⟨hfn_mem, hfn_pred⟩ := List.mem_filter.mp hfn
    simp [Bool.and_eq_true, BEq.beq, decide_eq_true_eq] at hfn_pred
    have hfn_name : fn.name = calleeName := hfn_pred.2
    have hname_eq : fn.name = witness.callee.name := by
      rw [hfn_name, hname]
    exact List.inj_on_of_nodup_map hnodup hfn_mem hmem hname_eq
  -- The filter of spec.functions is Nodup (sublist of a Nodup list)
  have hfilt_nodup : (spec.functions.filter (fun fn => fn.isInternal && fn.name == calleeName)).Nodup :=
    List.Nodup.filter _ (List.Nodup.of_map _ hnodup)
  -- The filter is nonempty, Nodup, and all elements equal witness.callee → it's [witness.callee]
  match hfilt : spec.functions.filter (fun fn => fn.isInternal && fn.name == calleeName) with
  | [fn] =>
      have hfn : fn = witness.callee := by
        apply hfilter_eq
        simpa [hfilt] using hin_filter
      simp [findUniqueInternalFunction?, hfilt, hfn]
  | [] =>
      cases (by simpa [hfilt] using hin_filter : False)
  | fn₁ :: fn₂ :: rest =>
      exfalso
      have hnd : (fn₁ :: fn₂ :: rest).Nodup := by
        simpa [hfilt] using hfilt_nodup
      have h1 : fn₁ = witness.callee := by
        apply hfilter_eq
        rw [hfilt]
        simp
      have h2 : fn₂ = witness.callee := by
        apply hfilter_eq
        rw [hfilt]
        simp
      rw [h1, h2] at hnd
      exact (List.nodup_cons.mp hnd).1 (by simp)

theorem directHelperTouchesUnsupportedConstructorRawCalldataSurface_eq_false_of_supported
    {spec : CompilationModel}
    {fn : FunctionSpec}
    (hHelpers : SupportedBodyHelperInterface spec fn)
    (hnodup : (spec.functions.map (·.name)).Nodup) :
    directHelperTouchesUnsupportedConstructorRawCalldataSurface spec fn = false := by
  unfold directHelperTouchesUnsupportedConstructorRawCalldataSurface
  apply List.any_eq_false.mpr
  intro calleeName hmem
  let witness := hHelpers.summaryOfCall hmem
  have hfind :
      findUniqueInternalFunction? spec calleeName = some witness.callee :=
    findUniqueInternalFunction?_of_witness witness hnodup
  simpa [hfind, witness] using witness.summary.constructorRawCalldataSurfaceClosed

theorem helperClosureTouchesUnsupportedConstructorRawCalldataSurface_eq_false_of_no_helper_calls
    {spec : CompilationModel}
    {fn : FunctionSpec}
    (fuel : Nat)
    (hnil : helperCallNames fn = []) :
    helperClosureTouchesUnsupportedConstructorRawCalldataSurface spec fuel fn = false := by
  cases fuel <;>
    simp [helperClosureTouchesUnsupportedConstructorRawCalldataSurface,
      helperClosureTouchesUnsupportedConstructorRawCalldataSurfaceFrom, hnil]

/-- Public characterization of `execStmtWithHelpers` for `Stmt.internalCallAssign`
when the callee is identified by a `SupportedInternalHelperWitness` and function
names are unique.  This avoids exposing the private `findUniqueInternalFunction?`
while giving external proofs full access to the semantic structure. -/
theorem execStmtWithHelpers_internalCallAssign_of_witness
    {spec : CompilationModel}
    {fields : List Field}
    {fuel : Nat}
    {state : RuntimeState}
    {names : List String}
    {calleeName : String}
    {args : List Expr}
    (witness : SupportedInternalHelperWitness spec calleeName)
    (hnodup : (spec.functions.map (·.name)).Nodup) :
    execStmtWithHelpers spec fields (fuel + 1) state
      (Stmt.internalCallAssign names calleeName args) =
    match evalExprListWithHelpers spec fields (fuel + 1) state args with
    | some argVals =>
        let hresult := interpretInternalFunctionFuel spec fuel witness.callee state.world argVals
        if hresult.success then
          match names, hresult.returnValue with
          | [name], some value =>
              .continue { state with
                world := hresult.world
                bindings := bindValue state.bindings name value
              }
          | _, _ => .revert
        else
          .revert
    | none => .revert := by
  cases hargs : evalExprListWithHelpers spec fields (fuel + 1) state args <;>
    simp [execStmtWithHelpers, findUniqueInternalFunction?_of_witness witness hnodup, hargs]

/-- Version of `execStmtWithHelpers_internalCallAssign_obeys_summary` that takes
a `SupportedInternalHelperWitness` instead of the private `findUniqueInternalFunction?`
hypothesis, enabling use from files that cannot reference the private definition. -/
theorem execStmtWithHelpers_internalCallAssign_obeys_summary_of_witness
    {spec : CompilationModel}
    {fields : List Field}
    {fuel : Nat}
    {state : RuntimeState}
    {names : List String}
    {calleeName : String}
    {args : List Expr}
    (witness : SupportedInternalHelperWitness spec calleeName)
    (hnodup : (spec.functions.map (·.name)).Nodup)
    (hsound : InternalHelperSummarySound spec witness.callee witness.summary.contract)
    {argVals : List Nat}
    (hargs : evalExprListWithHelpers spec fields fuel state args = some argVals) :
    let result := interpretInternalFunctionFuel spec fuel witness.callee state.world argVals
    witness.summary.contract.post fuel 0 state.world argVals
      result.success result.returnValue result.world :=
  execStmtWithHelpers_internalCallAssign_obeys_summary
    (names := names)
    (hfind := findUniqueInternalFunction?_of_witness witness hnodup)
    (hsound := hsound)
    (hargs := hargs)

/-- Public characterization of `execStmtWithHelpers` for `Stmt.internalCall`
(void call) via a `SupportedInternalHelperWitness` and function-name uniqueness. -/
theorem execStmtWithHelpers_internalCall_of_witness
    {spec : CompilationModel}
    {fields : List Field}
    {fuel : Nat}
    {state : RuntimeState}
    {calleeName : String}
    {args : List Expr}
    (witness : SupportedInternalHelperWitness spec calleeName)
    (hnodup : (spec.functions.map (·.name)).Nodup) :
    execStmtWithHelpers spec fields (fuel + 1) state
      (Stmt.internalCall calleeName args) =
    match evalExprListWithHelpers spec fields (fuel + 1) state args with
    | some argVals =>
        let hresult := interpretInternalFunctionFuel spec fuel witness.callee state.world argVals
        if hresult.success then
          .continue { state with world := hresult.world }
        else
          .revert
    | none => .revert := by
  cases hargs : evalExprListWithHelpers spec fields (fuel + 1) state args <;>
    simp [execStmtWithHelpers, findUniqueInternalFunction?_of_witness witness hnodup, hargs]

/-- Public characterization of `evalExprWithHelpers` for `Expr.internalCall`
(expression-position helper call) via a `SupportedInternalHelperWitness` and
function-name uniqueness. -/
theorem evalExprWithHelpers_internalCall_of_witness
    {spec : CompilationModel}
    {fields : List Field}
    {fuel : Nat}
    {state : RuntimeState}
    {calleeName : String}
    {args : List Expr}
    (witness : SupportedInternalHelperWitness spec calleeName)
    (hnodup : (spec.functions.map (·.name)).Nodup) :
    evalExprWithHelpers spec fields (fuel + 1) state
      (Expr.internalCall calleeName args) =
    (do let argVals ← evalExprListWithHelpers spec fields (fuel + 1) state args
        let hresult := interpretInternalFunctionFuel spec fuel witness.callee state.world argVals
        if hresult.success then hresult.returnValue else none) := by
  simpa [evalExprWithHelpers, findUniqueInternalFunction?_of_witness witness hnodup]

/-- Version of `evalExprWithHelpers_internalCall_obeys_summary` that takes a
`SupportedInternalHelperWitness` instead of the private
`findUniqueInternalFunction?` hypothesis. This is the source-expression helper
summary seam consumed by expression-context helper-call bridge proofs. -/
theorem evalExprWithHelpers_internalCall_obeys_summary_of_witness
    {spec : CompilationModel}
    {fields : List Field}
    {fuel : Nat}
    {state : RuntimeState}
    {calleeName : String}
    {args : List Expr}
    (witness : SupportedInternalHelperWitness spec calleeName)
    (hnodup : (spec.functions.map (·.name)).Nodup)
    (hsound : InternalHelperSummarySound spec witness.callee witness.summary.contract)
    {argVals : List Nat}
    (hargs : evalExprListWithHelpers spec fields fuel state args = some argVals) :
    let result := interpretInternalFunctionFuel spec fuel witness.callee state.world argVals
    witness.summary.contract.post fuel 0 state.world argVals
      result.success result.returnValue result.world :=
  evalExprWithHelpers_internalCall_obeys_summary
    (hfind := findUniqueInternalFunction?_of_witness witness hnodup)
    (hsound := hsound)
    (hargs := hargs)

/-- Source-side world-preservation consequence for expression-position helper
calls, packaged with public supported-helper witnesses. -/
theorem evalExprWithHelpers_internalCall_preserves_world_of_witness
    {spec : CompilationModel}
    {fields : List Field}
    {fuel : Nat}
    {state : RuntimeState}
    {calleeName : String}
    {args : List Expr}
    (witness : SupportedInternalHelperWitness spec calleeName)
    (hnodup : (spec.functions.map (·.name)).Nodup)
    (hsound : InternalHelperSummarySound spec witness.callee witness.summary.contract)
    (hpreserve : InternalHelperSummaryPreservesWorldOnSuccess witness.summary.contract)
    {argVals : List Nat}
    (hargs : evalExprListWithHelpers spec fields fuel state args = some argVals) :
    let result := interpretInternalFunctionFuel spec fuel witness.callee state.world argVals
    result.success = true → result.world = state.world := by
  intro result hsuccess
  exact helperSummaryPreservesWorldOnSuccess hpreserve
    (hpost := evalExprWithHelpers_internalCall_obeys_summary_of_witness
      (witness := witness)
      (hnodup := hnodup)
      (hsound := hsound)
      (hargs := hargs))
    hsuccess

theorem SupportedBodyHelperInterface.summarySoundOfCall
    {spec : CompilationModel}
    {fn : FunctionSpec}
    {calleeName : String}
    (hHelpers : SupportedBodyHelperInterface spec fn)
    (hsummaries : SupportedBodyHelperSummariesSound spec fn hHelpers)
    (hmem : calleeName ∈ helperCallNames fn) :
    InternalHelperSummarySound spec
      (hHelpers.summaryOfCall hmem).callee
      (hHelpers.summaryContractOfCall hmem) :=
  hsummaries calleeName hmem

theorem SupportedBodyHelperInterface.exprCallSummaryPreservesWorld
    {spec : CompilationModel}
    {fn : FunctionSpec}
    {calleeName : String}
    (hHelpers : SupportedBodyHelperInterface spec fn)
    (hmem : calleeName ∈ exprHelperCallNames fn) :
    let hcall : calleeName ∈ helperCallNames fn :=
      exprHelperCallNames_subset_helperCallNames hmem
    InternalHelperSummaryPreservesWorldOnSuccess
      (hHelpers.summaryContractOfCall hcall) :=
  hHelpers.exprSummaryPreservesWorld hmem

/-- Reusable global helper-summary proof inventory. This is the proof-carrying
counterpart to the positive helper witness inventory in `SupportedSpec.lean`:
each internal helper summary is proved once and can then be reused across every
caller that references the same witness. -/
structure SupportedHelperSummaryProofCatalog
    (spec : CompilationModel) : Prop where
  sound :
    ∀ calleeName (witness : SupportedInternalHelperWitness spec calleeName),
      InternalHelperSummarySound spec witness.callee witness.summary.contract

theorem SupportedHelperSummaryProofCatalog.soundOfWitness
    {spec : CompilationModel}
    (hCatalog : SupportedHelperSummaryProofCatalog spec)
    {calleeName : String}
    (witness : SupportedInternalHelperWitness spec calleeName) :
    InternalHelperSummarySound spec witness.callee witness.summary.contract :=
  hCatalog.sound calleeName witness

theorem SupportedBodyHelperSummariesSound_of_proofCatalog
    {spec : CompilationModel}
    {fn : FunctionSpec}
    (hHelpers : SupportedBodyHelperInterface spec fn)
    (hCatalog : SupportedHelperSummaryProofCatalog spec) :
    SupportedBodyHelperSummariesSound spec fn hHelpers := by
  intro calleeName hmem
  exact hCatalog.soundOfWitness (hHelpers.summaryOfCall hmem)

structure SupportedFunctionHelperProofs
    (spec : CompilationModel)
    (fn : FunctionSpec)
    (hSupported : SupportedFunction spec fn) : Prop where
  summariesSound :
    SupportedBodyHelperSummariesSound spec fn hSupported.body.calls.helpers

structure SupportedSpecHelperProofs
    (spec : CompilationModel)
    (selectors : List Nat)
    (hSupported : SupportedSpec spec selectors) : Prop where
  helperCatalog :
    SupportedHelperSummaryProofCatalog spec

theorem SupportedSpecHelperProofs.functionProofs
    {spec : CompilationModel}
    {selectors : List Nat}
    (hSupported : SupportedSpec spec selectors)
    (hProofs : SupportedSpecHelperProofs spec selectors hSupported)
    (fn : FunctionSpec)
    (hfn : fn ∈ selectorDispatchedFunctions spec) :
    SupportedFunctionHelperProofs spec fn
      (hSupported.supportedFunctionOfSelectorDispatched hfn) := by
  refine
    { summariesSound :=
        SupportedBodyHelperSummariesSound_of_proofCatalog
          (hHelpers := (hSupported.supportedFunctionOfSelectorDispatched hfn).body.calls.helpers)
          hProofs.helperCatalog }

theorem SupportedSpecHelperProofs.functionSummariesSound
    {spec : CompilationModel}
    {selectors : List Nat}
    (hSupported : SupportedSpec spec selectors)
    (hProofs : SupportedSpecHelperProofs spec selectors hSupported)
    {fn : FunctionSpec}
    (hfn : fn ∈ selectorDispatchedFunctions spec) :
    SupportedBodyHelperSummariesSound spec fn
      (hSupported.supportedFunctionOfSelectorDispatched hfn).body.calls.helpers :=
  (SupportedSpecHelperProofs.functionProofs hSupported hProofs fn hfn).summariesSound

/-!
### Compositional helper-summary reuse across callers (#1630)

`SupportedSpecHelperProofs` carries a single global proof catalog
(`helperCatalog : SupportedHelperSummaryProofCatalog spec`) in which every internal
helper summary is proved sound exactly once. The theorems below *thread that
one-time proof through to every caller and every syntactic call site*, which is the
reuse that whole-contract correctness needs: a helper proved once is consumed at
each call without re-discharging its summary.

* `helperCallSummarySound` delivers the summary-soundness fact at an arbitrary
  helper call site of any selector-dispatched function, sourced purely from the
  shared catalog in `hProofs`.
* `evalInternalCallObeysSummary`, `execInternalCallObeysSummary` and
  `execInternalCallAssignObeysSummary` specialise that fact to the three helper
  call shapes of the source semantics (expression position, void statement and
  assigning statement), landing the helper's summary contract directly on the
  interpreter result at the call site.
-/

/-- Summary soundness at a helper call site of a selector-dispatched caller,
obtained purely by reusing the once-proved global catalog carried in `hProofs`.
This is the compositional bridge for #1630: the same helper proof services every
caller, so callers never re-prove a helper they share. -/
theorem SupportedSpecHelperProofs.helperCallSummarySound
    {spec : CompilationModel}
    {selectors : List Nat}
    (hSupported : SupportedSpec spec selectors)
    (hProofs : SupportedSpecHelperProofs spec selectors hSupported)
    {fn : FunctionSpec}
    (hfn : fn ∈ selectorDispatchedFunctions spec)
    {calleeName : String}
    (hmem : calleeName ∈ helperCallNames fn) :
    InternalHelperSummarySound spec
      ((hSupported.supportedFunctionOfSelectorDispatched hfn).body.calls.helpers.summaryOfCall hmem).callee
      ((hSupported.supportedFunctionOfSelectorDispatched hfn).body.calls.helpers.summaryContractOfCall hmem) :=
  SupportedSpecHelperProofs.functionSummariesSound hSupported hProofs hfn calleeName hmem

/-- Expression-position helper call (`Expr.internalCall`) at a call site of a
selector-dispatched caller. The first conjunct is the *expression-shape*
characterization — `evalExprWithHelpers` on the `Expr.internalCall` node reduces to
the callee's return value — and the second lands the reused helper summary contract
on that callee result. The shape-specific reduction is what distinguishes this
theorem's *type* from the void- and assigning-statement variants below (they share
the summary payload but characterize different evaluators / AST shapes). The summary
fact is reused from the shared catalog via `helperCallSummarySound`. -/
theorem SupportedSpecHelperProofs.evalInternalCallObeysSummary
    {spec : CompilationModel}
    {selectors : List Nat}
    (hSupported : SupportedSpec spec selectors)
    (hProofs : SupportedSpecHelperProofs spec selectors hSupported)
    {fn : FunctionSpec}
    (hfn : fn ∈ selectorDispatchedFunctions spec)
    {calleeName : String}
    (hmem : calleeName ∈ helperCallNames fn)
    {fields : List Field}
    {fuel : Nat}
    {state : RuntimeState}
    {args : List Expr}
    {argVals : List Nat}
    (hargs : evalExprListWithHelpers spec fields (fuel + 1) state args = some argVals) :
    let witness := (hSupported.supportedFunctionOfSelectorDispatched hfn).body.calls.helpers.summaryOfCall hmem
    let result := interpretInternalFunctionFuel spec fuel witness.callee state.world argVals
    evalExprWithHelpers spec fields (fuel + 1) state (Expr.internalCall calleeName args)
        = (if result.success then result.returnValue else none)
      ∧ witness.summary.contract.post fuel 0 state.world argVals
          result.success result.returnValue result.world := by
  intro witness result
  refine ⟨?_, ?_⟩
  · simp +zetaDelta [evalExprWithHelpers_internalCall_of_witness witness hSupported.functionNamesNodup, hargs]
  · exact SupportedSpecHelperProofs.helperCallSummarySound hSupported hProofs hfn hmem
      fuel state.world argVals

/-- Void-statement helper call (`Stmt.internalCall`) at a call site of a
selector-dispatched caller. The first conjunct is the *void-statement-shape*
characterization — `execStmtWithHelpers` on the `Stmt.internalCall` node reduces to a
world update (or revert) driven by the callee result — and the second lands the
reused helper summary contract on that result. The reduction over
`execStmtWithHelpers`/`Stmt.internalCall` distinguishes this theorem's type from the
expression-position and assigning-statement variants. -/
theorem SupportedSpecHelperProofs.execInternalCallObeysSummary
    {spec : CompilationModel}
    {selectors : List Nat}
    (hSupported : SupportedSpec spec selectors)
    (hProofs : SupportedSpecHelperProofs spec selectors hSupported)
    {fn : FunctionSpec}
    (hfn : fn ∈ selectorDispatchedFunctions spec)
    {calleeName : String}
    (hmem : calleeName ∈ helperCallNames fn)
    {fields : List Field}
    {fuel : Nat}
    {state : RuntimeState}
    {args : List Expr}
    {argVals : List Nat}
    (hargs : evalExprListWithHelpers spec fields (fuel + 1) state args = some argVals) :
    let witness := (hSupported.supportedFunctionOfSelectorDispatched hfn).body.calls.helpers.summaryOfCall hmem
    let result := interpretInternalFunctionFuel spec fuel witness.callee state.world argVals
    execStmtWithHelpers spec fields (fuel + 1) state (Stmt.internalCall calleeName args)
        = (if result.success then .continue { state with world := result.world } else .revert)
      ∧ witness.summary.contract.post fuel 0 state.world argVals
          result.success result.returnValue result.world := by
  intro witness result
  refine ⟨?_, ?_⟩
  · simp +zetaDelta [execStmtWithHelpers_internalCall_of_witness witness hSupported.functionNamesNodup, hargs]
  · exact SupportedSpecHelperProofs.helperCallSummarySound hSupported hProofs hfn hmem
      fuel state.world argVals

/-- Assigning-statement helper call (`Stmt.internalCallAssign`) at a call site of
a selector-dispatched caller. The first conjunct is the *assigning-statement-shape*
characterization — `execStmtWithHelpers` on the `Stmt.internalCallAssign names …`
node reduces to a single-name binding update on success — and the second lands the
reused helper summary contract on the callee result. The reduction over
`Stmt.internalCallAssign` (carrying `names`) distinguishes this theorem's type from
the expression-position and void-statement variants. -/
theorem SupportedSpecHelperProofs.execInternalCallAssignObeysSummary
    {spec : CompilationModel}
    {selectors : List Nat}
    (hSupported : SupportedSpec spec selectors)
    (hProofs : SupportedSpecHelperProofs spec selectors hSupported)
    {fn : FunctionSpec}
    (hfn : fn ∈ selectorDispatchedFunctions spec)
    {calleeName : String}
    (hmem : calleeName ∈ helperCallNames fn)
    {fields : List Field}
    {fuel : Nat}
    {state : RuntimeState}
    {names : List String}
    {args : List Expr}
    {argVals : List Nat}
    (hargs : evalExprListWithHelpers spec fields (fuel + 1) state args = some argVals) :
    let witness := (hSupported.supportedFunctionOfSelectorDispatched hfn).body.calls.helpers.summaryOfCall hmem
    let result := interpretInternalFunctionFuel spec fuel witness.callee state.world argVals
    execStmtWithHelpers spec fields (fuel + 1) state (Stmt.internalCallAssign names calleeName args)
        = (if result.success then
            match names, result.returnValue with
            | [name], some value =>
                .continue { state with
                  world := result.world
                  bindings := bindValue state.bindings name value }
            | _, _ => .revert
          else .revert)
      ∧ witness.summary.contract.post fuel 0 state.world argVals
          result.success result.returnValue result.world := by
  intro witness result
  refine ⟨?_, ?_⟩
  · simp +zetaDelta [execStmtWithHelpers_internalCallAssign_of_witness witness hSupported.functionNamesNodup, hargs]
  · exact SupportedSpecHelperProofs.helperCallSummarySound hSupported hProofs hfn hmem
      fuel state.world argVals

set_option maxHeartbeats 800000 in
mutual
  private theorem exprList_all_helperSurfaceClosed
      {exprs : List Expr}
      (hsurface : exprListTouchesUnsupportedHelperSurface exprs = false) :
      exprs.all (fun expr => exprTouchesUnsupportedHelperSurface expr == false) = true := by
    induction exprs with
    | nil =>
        rfl
    | cons expr rest ih =>
        simp only [exprListTouchesUnsupportedHelperSurface, Bool.or_eq_false_iff] at hsurface
        have hrest := ih hsurface.2
        simp only [List.all_cons, hsurface.1, hrest]
        rfl

  theorem evalExprWithHelpers_eq_evalExpr_of_helperSurfaceClosed
      (spec : CompilationModel)
      (fields : List Field)
      (fuel : Nat)
      (state : RuntimeState)
      (expr : Expr)
      (hsurface : exprTouchesUnsupportedHelperSurface expr = false) :
      evalExprWithHelpers spec fields fuel state expr = evalExpr fields state expr := by
    set_option maxHeartbeats 800000 in
    cases expr with
    | internalCall _ _ =>
        simp [exprTouchesUnsupportedHelperSurface] at hsurface
    | intrinsic _ _ _ _ =>
        simp [exprTouchesUnsupportedHelperSurface] at hsurface
    | adtConstruct _ _ _ | adtTag _ _ | adtField _ _ _ _ _ =>
        simp [exprTouchesUnsupportedHelperSurface] at hsurface
    | mappingChain _ _ =>
        simp [exprTouchesUnsupportedHelperSurface] at hsurface
    | literal _ =>
        simpa [evalExprWithHelpers, evalExpr_literal]
    | param _ =>
        simpa [evalExprWithHelpers, evalExpr_param]
    | immutable _ =>
        simpa [evalExprWithHelpers, evalExpr_immutable]
    | localVar _ =>
        simpa [evalExprWithHelpers, evalExpr_localVar]
    | caller | contractAddress | txOrigin | chainid | msgValue | selfBalance | blockTimestamp | blockNumber | blobbasefee
    | calldatasize =>
        simp [evalExprWithHelpers, evalExpr_caller, evalExpr_contractAddress, evalExpr_txOrigin, evalExpr_chainid,
          evalExpr_msgValue, evalExpr_selfBalance, evalExpr_blockTimestamp, evalExpr_blockNumber, evalExpr_blobbasefee,
          evalExpr_calldatasize]
    | storage _ =>
        simpa [evalExprWithHelpers, evalExpr_storage]
    | storageAddr _ =>
        simpa [evalExprWithHelpers, evalExpr_storageAddr]
    | storageArrayLength _ =>
        simpa [evalExprWithHelpers, evalExpr_storageArrayLength]
    | constructorArg _ | returndataSize =>
        simp [evalExprWithHelpers, evalExpr_constructorArg,
          evalExpr_returndataSize]
    | arrayLength _ =>
        simpa [evalExprWithHelpers, evalExpr_arrayLength]
    | memoryArrayLength _ =>
        simpa [evalExprWithHelpers, evalExpr_memoryArrayLength]
    | dynamicBytesEq _ _ =>
        simpa [evalExprWithHelpers, evalExpr_dynamicBytesEq]
    | externalCall name args =>
        cases args with
        | nil => simp [evalExprWithHelpers, evalExpr_externalCall_of_arity]
        | cons base tl =>
          cases tl with
          | nil => simp [evalExprWithHelpers, evalExpr_externalCall_of_arity]
          | cons exponent tl' =>
            cases tl' with
            | cons _ _ => simp [evalExprWithHelpers, evalExpr_externalCall_of_arity]
            | nil =>
              by_cases hname : name = builtinExpName
              · subst hname
                simp only [exprTouchesUnsupportedHelperSurface, beq_self_eq_true, if_true,
                  Bool.or_eq_false_iff] at hsurface
                have hbase := evalExprWithHelpers_eq_evalExpr_of_helperSurfaceClosed
                  spec fields fuel state base hsurface.1
                have hexp := evalExprWithHelpers_eq_evalExpr_of_helperSurfaceClosed
                  spec fields fuel state exponent hsurface.2
                simp [evalExprWithHelpers, evalExpr_externalCall_builtinExp, hbase, hexp,
                  Verity.Core.Uint256.powEff_eq_pow]
              · simp [evalExprWithHelpers, evalExpr_externalCall_of_ne _ _ _ _ hname, hname]
    | mload a =>
        simp only [exprTouchesUnsupportedHelperSurface] at hsurface
        have ha :=
          evalExprWithHelpers_eq_evalExpr_of_helperSurfaceClosed spec fields fuel state a hsurface
        simp [evalExprWithHelpers, evalExpr_mload, ha]
    | tload a =>
        simp only [exprTouchesUnsupportedHelperSurface] at hsurface
        have ha :=
          evalExprWithHelpers_eq_evalExpr_of_helperSurfaceClosed spec fields fuel state a hsurface
        simp [evalExprWithHelpers, evalExpr_tload, ha]
    | calldataload a =>
        simp only [exprTouchesUnsupportedHelperSurface] at hsurface
        have ha :=
          evalExprWithHelpers_eq_evalExpr_of_helperSurfaceClosed spec fields fuel state a hsurface
        simp [evalExprWithHelpers, evalExpr_calldataload, ha]
    | extcodesize a =>
        simp only [exprTouchesUnsupportedHelperSurface] at hsurface
        have ha :=
          evalExprWithHelpers_eq_evalExpr_of_helperSurfaceClosed spec fields fuel state a hsurface
        simp [evalExprWithHelpers, evalExpr_extcodesize, ha]
    | returndataOptionalBoolAt a =>
        simp only [exprTouchesUnsupportedHelperSurface] at hsurface
        have ha :=
          evalExprWithHelpers_eq_evalExpr_of_helperSurfaceClosed spec fields fuel state a hsurface
        simp [evalExprWithHelpers, evalExpr_returndataOptionalBoolAt, ha]
    | keccak256 a b =>
        simp only [exprTouchesUnsupportedHelperSurface, Bool.or_eq_false_iff] at hsurface
        have ha :=
          evalExprWithHelpers_eq_evalExpr_of_helperSurfaceClosed spec fields fuel state a hsurface.1
        have hb :=
          evalExprWithHelpers_eq_evalExpr_of_helperSurfaceClosed spec fields fuel state b hsurface.2
        simpa [evalExprWithHelpers, evalExpr_keccak256, ha, hb]
    | call g t v io is oo os =>
        simpa [evalExprWithHelpers, evalExpr_call]
    | staticcall g t io is oo os =>
        simpa [evalExprWithHelpers, evalExpr_staticcall]
    | delegatecall g t io is oo os =>
        simpa [evalExprWithHelpers, evalExpr_delegatecall]
    | add a b | sub a b | mul a b | div a b | mod a b =>
        simp only [exprTouchesUnsupportedHelperSurface, Bool.or_eq_false_iff] at hsurface
        have ha :=
          evalExprWithHelpers_eq_evalExpr_of_helperSurfaceClosed spec fields fuel state a hsurface.1
        have hb :=
          evalExprWithHelpers_eq_evalExpr_of_helperSurfaceClosed spec fields fuel state b hsurface.2
        simpa [evalExprWithHelpers, evalExpr_add, evalExpr_sub, evalExpr_mul, evalExpr_div,
          evalExpr_mod, ha, hb]
    | eq a b | ge a b | gt a b | lt a b | le a b
    | logicalAnd a b | logicalOr a b =>
        simp only [exprTouchesUnsupportedHelperSurface, Bool.or_eq_false_iff] at hsurface
        have ha :=
          evalExprWithHelpers_eq_evalExpr_of_helperSurfaceClosed spec fields fuel state a hsurface.1
        have hb :=
          evalExprWithHelpers_eq_evalExpr_of_helperSurfaceClosed spec fields fuel state b hsurface.2
        simpa [evalExprWithHelpers, evalExpr_eq, evalExpr_ge, evalExpr_gt, evalExpr_lt,
          evalExpr_le, evalExpr_logicalAnd, evalExpr_logicalOr, ha, hb]
    | sdiv a b | smod a b | sgt a b | slt a b =>
        simp only [exprTouchesUnsupportedHelperSurface, Bool.or_eq_false_iff] at hsurface
        have ha :=
          evalExprWithHelpers_eq_evalExpr_of_helperSurfaceClosed spec fields fuel state a hsurface.1
        have hb :=
          evalExprWithHelpers_eq_evalExpr_of_helperSurfaceClosed spec fields fuel state b hsurface.2
        simpa [evalExprWithHelpers, evalExpr_sdiv, evalExpr_smod, evalExpr_sgt, evalExpr_slt, ha, hb]
    | bitAnd a b | bitOr a b | bitXor a b | min a b | max a b | wMulDown a b | wDivUp a b =>
        simp only [exprTouchesUnsupportedHelperSurface, Bool.or_eq_false_iff] at hsurface
        have ha :=
          evalExprWithHelpers_eq_evalExpr_of_helperSurfaceClosed spec fields fuel state a hsurface.1
        have hb :=
          evalExprWithHelpers_eq_evalExpr_of_helperSurfaceClosed spec fields fuel state b hsurface.2
        simpa [evalExprWithHelpers, evalExpr_bitAnd, evalExpr_bitOr, evalExpr_bitXor,
          evalExpr_min, evalExpr_max, evalExpr_wMulDown, evalExpr_wDivUp, ha, hb]
    | shl a b | shr a b =>
        simp only [exprTouchesUnsupportedHelperSurface, Bool.or_eq_false_iff] at hsurface
        have ha :=
          evalExprWithHelpers_eq_evalExpr_of_helperSurfaceClosed spec fields fuel state a hsurface.1
        have hb :=
          evalExprWithHelpers_eq_evalExpr_of_helperSurfaceClosed spec fields fuel state b hsurface.2
        simpa [evalExprWithHelpers, evalExpr_shl, evalExpr_shr, ha, hb]
    | sar a b =>
        simp only [exprTouchesUnsupportedHelperSurface, Bool.or_eq_false_iff] at hsurface
        have ha :=
          evalExprWithHelpers_eq_evalExpr_of_helperSurfaceClosed spec fields fuel state a hsurface.1
        have hb :=
          evalExprWithHelpers_eq_evalExpr_of_helperSurfaceClosed spec fields fuel state b hsurface.2
        simpa [evalExprWithHelpers, evalExpr_sar, ha, hb]
    | byte a b =>
        simp only [exprTouchesUnsupportedHelperSurface, Bool.or_eq_false_iff] at hsurface
        have ha :=
          evalExprWithHelpers_eq_evalExpr_of_helperSurfaceClosed spec fields fuel state a hsurface.1
        have hb :=
          evalExprWithHelpers_eq_evalExpr_of_helperSurfaceClosed spec fields fuel state b hsurface.2
        simpa [evalExprWithHelpers, evalExpr_byte, ha, hb]
    | signextend a b =>
        simp only [exprTouchesUnsupportedHelperSurface, Bool.or_eq_false_iff] at hsurface
        have ha :=
          evalExprWithHelpers_eq_evalExpr_of_helperSurfaceClosed spec fields fuel state a hsurface.1
        have hb :=
          evalExprWithHelpers_eq_evalExpr_of_helperSurfaceClosed spec fields fuel state b hsurface.2
        simpa [evalExprWithHelpers, evalExpr_signextend, ha, hb]
    | bitNot a | logicalNot a =>
        simp only [exprTouchesUnsupportedHelperSurface] at hsurface
        have ha :=
          evalExprWithHelpers_eq_evalExpr_of_helperSurfaceClosed spec fields fuel state a hsurface
        simpa [evalExprWithHelpers, evalExpr_bitNot, evalExpr_logicalNot, ha]
    | mapping _ b | mappingUint _ b =>
        simp only [exprTouchesUnsupportedHelperSurface] at hsurface
        have hb :=
          evalExprWithHelpers_eq_evalExpr_of_helperSurfaceClosed spec fields fuel state b hsurface
        simpa [evalExprWithHelpers, evalExpr_mapping, evalExpr_mappingUint, hb]
    | arrayElement _ b =>
        simp [exprTouchesUnsupportedHelperSurface] at hsurface
    | memoryArrayElement _ b =>
        simp only [exprTouchesUnsupportedHelperSurface] at hsurface
        have hb :=
          evalExprWithHelpers_eq_evalExpr_of_helperSurfaceClosed spec fields fuel state b hsurface
        simp [evalExprWithHelpers, evalExpr_memoryArrayElement, hb,
          SourceSemantics.wordNormalize_eq_mod]
    | arrayElementWord _ b _ _ =>
        simp [evalExprWithHelpers, evalExpr_arrayElementWord]
    | arrayElementDynamicWord _ b _ =>
        simp only [exprTouchesUnsupportedHelperSurface] at hsurface
        have hb :=
          evalExprWithHelpers_eq_evalExpr_of_helperSurfaceClosed spec fields fuel state b hsurface
        simp only [evalExprWithHelpers, evalExpr_arrayElementDynamicWord, hb]
    | arrayElementDynamicDataOffset _ b =>
        simp only [exprTouchesUnsupportedHelperSurface] at hsurface
        have hb :=
          evalExprWithHelpers_eq_evalExpr_of_helperSurfaceClosed spec fields fuel state b hsurface
        simp only [evalExprWithHelpers, evalExpr_arrayElementDynamicDataOffset, hb]
    | arrayElementDynamicMemberLength _ b _ =>
        simp only [exprTouchesUnsupportedHelperSurface] at hsurface
        have hb :=
          evalExprWithHelpers_eq_evalExpr_of_helperSurfaceClosed spec fields fuel state b hsurface
        simp only [evalExprWithHelpers, evalExpr_arrayElementDynamicMemberLength, hb]
    | arrayElementDynamicMemberDataOffset _ b _ =>
        simp only [exprTouchesUnsupportedHelperSurface] at hsurface
        have hb :=
          evalExprWithHelpers_eq_evalExpr_of_helperSurfaceClosed spec fields fuel state b hsurface
        simp only [evalExprWithHelpers, evalExpr_arrayElementDynamicMemberDataOffset, hb]
    | arrayElementDynamicMemberElement _ a _ b =>
        simp only [exprTouchesUnsupportedHelperSurface, Bool.or_eq_false_iff] at hsurface
        have ha :=
          evalExprWithHelpers_eq_evalExpr_of_helperSurfaceClosed spec fields fuel state a hsurface.1
        have hb :=
          evalExprWithHelpers_eq_evalExpr_of_helperSurfaceClosed spec fields fuel state b hsurface.2
        simp only [evalExprWithHelpers, evalExpr_arrayElementDynamicMemberElement, ha, hb]
    | mappingWord _ b _ | mappingPackedWord _ b _ _ | structMember _ b _ =>
        simp only [exprTouchesUnsupportedHelperSurface] at hsurface
        have hb :=
          evalExprWithHelpers_eq_evalExpr_of_helperSurfaceClosed spec fields fuel state b hsurface
        simpa [evalExprWithHelpers, evalExpr_mappingWord, evalExpr_mappingPackedWord,
          evalExpr_structMember, hb]
    | storageArrayElement fieldName b =>
        simp only [exprTouchesUnsupportedHelperSurface] at hsurface
        have hb :=
          evalExprWithHelpers_eq_evalExpr_of_helperSurfaceClosed spec fields fuel state b hsurface
        simpa [evalExprWithHelpers, evalExpr_storageArrayElement, hb]
    | mapping2 _ a b | mapping2Word _ a b _ | structMember2 _ a b _ =>
        simp only [exprTouchesUnsupportedHelperSurface, Bool.or_eq_false_iff] at hsurface
        have ha :=
          evalExprWithHelpers_eq_evalExpr_of_helperSurfaceClosed spec fields fuel state a hsurface.1
        have hb :=
          evalExprWithHelpers_eq_evalExpr_of_helperSurfaceClosed spec fields fuel state b hsurface.2
        simpa [evalExprWithHelpers, evalExpr_mapping2, evalExpr_mapping2Word,
          evalExpr_structMember2, ha, hb]
    | ceilDiv a b =>
        simp only [exprTouchesUnsupportedHelperSurface, Bool.or_eq_false_iff] at hsurface
        have ha :=
          evalExprWithHelpers_eq_evalExpr_of_helperSurfaceClosed spec fields fuel state a hsurface.1
        have hb :=
          evalExprWithHelpers_eq_evalExpr_of_helperSurfaceClosed spec fields fuel state b hsurface.2
        simpa [evalExprWithHelpers, evalExpr_ceilDiv, ha, hb]
    | mulDivDown a b c | mulDivUp a b c =>
        simp only [exprTouchesUnsupportedHelperSurface, Bool.or_eq_false_iff] at hsurface
        have ha :=
          evalExprWithHelpers_eq_evalExpr_of_helperSurfaceClosed spec fields fuel state a hsurface.1.1
        have hb :=
          evalExprWithHelpers_eq_evalExpr_of_helperSurfaceClosed spec fields fuel state b hsurface.1.2
        have hc :=
          evalExprWithHelpers_eq_evalExpr_of_helperSurfaceClosed spec fields fuel state c hsurface.2
        simpa [evalExprWithHelpers, evalExpr_mulDivDown, evalExpr_mulDivUp, ha, hb, hc]
    | mulDiv512Down _ _ _ | mulDiv512Up _ _ _ =>
        simp [evalExprWithHelpers, evalExpr_mulDiv512Down, evalExpr_mulDiv512Up]
    | paramDynamicHeadWord _ _ =>
        simp [evalExprWithHelpers, evalExpr_paramDynamicHeadWord]
    | paramDynamicStaticComposite _ _ =>
        simp [evalExprWithHelpers, evalExpr_paramDynamicStaticComposite]
    | paramDynamicMemberLength _ _ | paramDynamicMemberDataOffset _ _ =>
        simp [evalExprWithHelpers, evalExpr_paramDynamicMemberLength,
          evalExpr_paramDynamicMemberDataOffset]
    | paramDynamicMemberElement _ _ b =>
        simp only [exprTouchesUnsupportedHelperSurface] at hsurface
        have hb :=
          evalExprWithHelpers_eq_evalExpr_of_helperSurfaceClosed spec fields fuel state b hsurface
        simpa [evalExprWithHelpers, evalExpr_paramDynamicMemberElement, hb]
    | ite cond thenVal elseVal =>
        simp only [exprTouchesUnsupportedHelperSurface, Bool.or_eq_false_iff] at hsurface
        have hcond :=
          evalExprWithHelpers_eq_evalExpr_of_helperSurfaceClosed spec fields fuel state cond hsurface.1.1
        have hthen :=
          evalExprWithHelpers_eq_evalExpr_of_helperSurfaceClosed spec fields fuel state thenVal hsurface.1.2
        have helse :=
          evalExprWithHelpers_eq_evalExpr_of_helperSurfaceClosed spec fields fuel state elseVal hsurface.2
        simpa [evalExprWithHelpers, evalExpr_ite, hcond, hthen, helse]
    | forkIfAtLeast required thenExpr elseExpr =>
        simpa [evalExprWithHelpers, evalExpr_forkIfAtLeast]

  theorem evalExprListWithHelpers_eq_evalExprList_of_helperSurfaceClosed
      (spec : CompilationModel)
      (fields : List Field)
      (fuel : Nat)
      (state : RuntimeState)
      (exprs : List Expr)
      (hsurface : exprs.all (fun expr => exprTouchesUnsupportedHelperSurface expr == false) = true) :
      evalExprListWithHelpers spec fields fuel state exprs =
        exprs.mapM (evalExpr fields state) := by
    induction exprs with
    | nil =>
        simp [evalExprListWithHelpers]
    | cons expr rest ih =>
        simp only [List.all_cons, Bool.and_eq_true] at hsurface
        simp [evalExprListWithHelpers,
          evalExprWithHelpers_eq_evalExpr_of_helperSurfaceClosed
            spec fields fuel state expr (by simpa using hsurface.1),
          ih hsurface.2]

  private theorem evalExprList_eq_mapM
      (fields : List Field)
      (state : RuntimeState)
      (exprs : List Expr) :
      evalExprList fields state exprs = exprs.mapM (evalExpr fields state) := by
    induction exprs with
    | nil =>
        rfl
    | cons expr rest ih =>
        simp [evalExprList, ih]
  
  private theorem execStmtWithHelpers_eq_execStmt_of_helperSurfaceClosed_setMapping
      (spec : CompilationModel)
      (fields : List Field)
      (fuel : Nat)
      (state : RuntimeState)
      (fieldName : String)
      (key value : Expr)
      (hsurface : stmtTouchesUnsupportedHelperSurface (.setMapping fieldName key value) = false) :
      execStmtWithHelpers spec fields fuel state (.setMapping fieldName key value) =
        execStmtWithEvents fields spec.events state (.setMapping fieldName key value) := by
    simp only [stmtTouchesUnsupportedHelperSurface, Bool.or_eq_false_iff] at hsurface
    simp [execStmtWithHelpers, execStmtWithEvents,
      evalExprWithHelpers_eq_evalExpr_of_helperSurfaceClosed spec fields fuel state key hsurface.1,
      evalExprWithHelpers_eq_evalExpr_of_helperSurfaceClosed spec fields fuel state value hsurface.2]

  private theorem execStmtWithHelpers_eq_execStmt_of_helperSurfaceClosed_setMappingWord
      (spec : CompilationModel)
      (fields : List Field)
      (fuel : Nat)
      (state : RuntimeState)
      (fieldName : String)
      (key value : Expr)
      (wordOffset : Nat)
      (hsurface : stmtTouchesUnsupportedHelperSurface (.setMappingWord fieldName key wordOffset value) = false) :
      execStmtWithHelpers spec fields fuel state (.setMappingWord fieldName key wordOffset value) =
        execStmtWithEvents fields spec.events state (.setMappingWord fieldName key wordOffset value) := by
    simp only [stmtTouchesUnsupportedHelperSurface, Bool.or_eq_false_iff] at hsurface
    simp [execStmtWithHelpers, execStmtWithEvents,
      evalExprWithHelpers_eq_evalExpr_of_helperSurfaceClosed spec fields fuel state key hsurface.1,
      evalExprWithHelpers_eq_evalExpr_of_helperSurfaceClosed spec fields fuel state value hsurface.2]

  private theorem execStmtWithHelpers_eq_execStmt_of_helperSurfaceClosed_setMappingPackedWord
      (spec : CompilationModel)
      (fields : List Field)
      (fuel : Nat)
      (state : RuntimeState)
      (fieldName : String)
      (key value : Expr)
      (wordOffset : Nat)
      (packed : PackedBits)
      (hsurface :
        stmtTouchesUnsupportedHelperSurface (.setMappingPackedWord fieldName key wordOffset packed value) = false) :
      execStmtWithHelpers spec fields fuel state
          (.setMappingPackedWord fieldName key wordOffset packed value) =
        execStmtWithEvents fields spec.events state (.setMappingPackedWord fieldName key wordOffset packed value) := by
    simp only [stmtTouchesUnsupportedHelperSurface, Bool.or_eq_false_iff] at hsurface
    simp [execStmtWithHelpers, execStmtWithEvents,
      evalExprWithHelpers_eq_evalExpr_of_helperSurfaceClosed spec fields fuel state key hsurface.1,
      evalExprWithHelpers_eq_evalExpr_of_helperSurfaceClosed spec fields fuel state value hsurface.2]

  private theorem execStmtWithHelpers_eq_execStmt_of_helperSurfaceClosed_setMappingUint
      (spec : CompilationModel)
      (fields : List Field)
      (fuel : Nat)
      (state : RuntimeState)
      (fieldName : String)
      (key value : Expr)
      (hsurface : stmtTouchesUnsupportedHelperSurface (.setMappingUint fieldName key value) = false) :
      execStmtWithHelpers spec fields fuel state (.setMappingUint fieldName key value) =
        execStmtWithEvents fields spec.events state (.setMappingUint fieldName key value) := by
    simp only [stmtTouchesUnsupportedHelperSurface, Bool.or_eq_false_iff] at hsurface
    simp [execStmtWithHelpers, execStmtWithEvents,
      evalExprWithHelpers_eq_evalExpr_of_helperSurfaceClosed spec fields fuel state key hsurface.1,
      evalExprWithHelpers_eq_evalExpr_of_helperSurfaceClosed spec fields fuel state value hsurface.2]

  private theorem execStmtWithHelpers_eq_execStmt_of_helperSurfaceClosed_setStructMember
      (spec : CompilationModel)
      (fields : List Field)
      (fuel : Nat)
      (state : RuntimeState)
      (fieldName memberName : String)
      (key value : Expr)
      (hsurface : stmtTouchesUnsupportedHelperSurface (.setStructMember fieldName key memberName value) = false) :
      execStmtWithHelpers spec fields fuel state (.setStructMember fieldName key memberName value) =
        execStmtWithEvents fields spec.events state (.setStructMember fieldName key memberName value) := by
    simp only [stmtTouchesUnsupportedHelperSurface, Bool.or_eq_false_iff] at hsurface
    simp [execStmtWithHelpers, execStmtWithEvents,
      evalExprWithHelpers_eq_evalExpr_of_helperSurfaceClosed spec fields fuel state key hsurface.1,
      evalExprWithHelpers_eq_evalExpr_of_helperSurfaceClosed spec fields fuel state value hsurface.2]

  private theorem execStmtWithHelpers_eq_execStmt_of_helperSurfaceClosed_keyListValue
      (spec : CompilationModel)
      (fields : List Field)
      (fuel : Nat)
      (state : RuntimeState)
      (fieldName : String)
      (keys : List Expr)
      (value : Expr)
      (hsurface : stmtTouchesUnsupportedHelperSurface (.setMappingChain fieldName keys value) = false) :
      execStmtWithHelpers spec fields fuel state (.setMappingChain fieldName keys value) =
        execStmtWithEvents fields spec.events state (.setMappingChain fieldName keys value) := by
    simp only [stmtTouchesUnsupportedHelperSurface, Bool.or_eq_false_iff] at hsurface
    have hkeys :
        keys.all (fun expr => exprTouchesUnsupportedHelperSurface expr == false) = true :=
      exprList_all_helperSurfaceClosed hsurface.1
    have hvalue :=
      evalExprWithHelpers_eq_evalExpr_of_helperSurfaceClosed spec fields fuel state value hsurface.2
    unfold execStmtWithHelpers execStmtWithEvents
    rw [evalExprListWithHelpers_eq_evalExprList_of_helperSurfaceClosed spec fields fuel state keys hkeys, hvalue]
    rw [evalExprList_eq_mapM]

  private theorem execStmtWithHelpers_eq_execStmt_of_helperSurfaceClosed_setMapping2
      (spec : CompilationModel)
      (fields : List Field)
      (fuel : Nat)
      (state : RuntimeState)
      (fieldName : String)
      (key1 key2 value : Expr)
      (hsurface : stmtTouchesUnsupportedHelperSurface (.setMapping2 fieldName key1 key2 value) = false) :
      execStmtWithHelpers spec fields fuel state (.setMapping2 fieldName key1 key2 value) =
        execStmtWithEvents fields spec.events state (.setMapping2 fieldName key1 key2 value) := by
    simp only [stmtTouchesUnsupportedHelperSurface, Bool.or_eq_false_iff, Bool.or_assoc] at hsurface
    simp [execStmtWithHelpers, execStmtWithEvents,
      evalExprWithHelpers_eq_evalExpr_of_helperSurfaceClosed spec fields fuel state key1 hsurface.1,
      evalExprWithHelpers_eq_evalExpr_of_helperSurfaceClosed spec fields fuel state key2 hsurface.2.1,
      evalExprWithHelpers_eq_evalExpr_of_helperSurfaceClosed spec fields fuel state value hsurface.2.2]

  private theorem execStmtWithHelpers_eq_execStmt_of_helperSurfaceClosed_setMapping2Word
      (spec : CompilationModel)
      (fields : List Field)
      (fuel : Nat)
      (state : RuntimeState)
      (fieldName : String)
      (key1 key2 value : Expr)
      (wordOffset : Nat)
      (hsurface : stmtTouchesUnsupportedHelperSurface (.setMapping2Word fieldName key1 key2 wordOffset value) = false) :
      execStmtWithHelpers spec fields fuel state (.setMapping2Word fieldName key1 key2 wordOffset value) =
        execStmtWithEvents fields spec.events state (.setMapping2Word fieldName key1 key2 wordOffset value) := by
    simp only [stmtTouchesUnsupportedHelperSurface, Bool.or_eq_false_iff, Bool.or_assoc] at hsurface
    simp [execStmtWithHelpers, execStmtWithEvents,
      evalExprWithHelpers_eq_evalExpr_of_helperSurfaceClosed spec fields fuel state key1 hsurface.1,
      evalExprWithHelpers_eq_evalExpr_of_helperSurfaceClosed spec fields fuel state key2 hsurface.2.1,
      evalExprWithHelpers_eq_evalExpr_of_helperSurfaceClosed spec fields fuel state value hsurface.2.2]

  private theorem execStmtWithHelpers_eq_execStmt_of_helperSurfaceClosed_setStructMember2
      (spec : CompilationModel)
      (fields : List Field)
      (fuel : Nat)
      (state : RuntimeState)
      (fieldName memberName : String)
      (key1 key2 value : Expr)
      (hsurface :
        stmtTouchesUnsupportedHelperSurface (.setStructMember2 fieldName key1 key2 memberName value) = false) :
      execStmtWithHelpers spec fields fuel state (.setStructMember2 fieldName key1 key2 memberName value) =
        execStmtWithEvents fields spec.events state (.setStructMember2 fieldName key1 key2 memberName value) := by
    simp only [stmtTouchesUnsupportedHelperSurface, Bool.or_eq_false_iff, Bool.or_assoc] at hsurface
    simp [execStmtWithHelpers, execStmtWithEvents,
      evalExprWithHelpers_eq_evalExpr_of_helperSurfaceClosed spec fields fuel state key1 hsurface.1,
      evalExprWithHelpers_eq_evalExpr_of_helperSurfaceClosed spec fields fuel state key2 hsurface.2.1,
      evalExprWithHelpers_eq_evalExpr_of_helperSurfaceClosed spec fields fuel state value hsurface.2.2]

  private theorem execStmtWithHelpers_eq_execStmt_of_helperSurfaceClosed_setStorageArrayElement
      (spec : CompilationModel)
      (fields : List Field)
      (fuel : Nat)
      (state : RuntimeState)
      (fieldName : String)
      (index value : Expr)
      (hsurface : stmtTouchesUnsupportedHelperSurface (.setStorageArrayElement fieldName index value) = false) :
      execStmtWithHelpers spec fields fuel state (.setStorageArrayElement fieldName index value) =
        execStmtWithEvents fields spec.events state (.setStorageArrayElement fieldName index value) := by
    simp only [stmtTouchesUnsupportedHelperSurface, Bool.or_eq_false_iff] at hsurface
    simp [execStmtWithHelpers, execStmtWithEvents,
      evalExprWithHelpers_eq_evalExpr_of_helperSurfaceClosed spec fields fuel state index hsurface.1,
      evalExprWithHelpers_eq_evalExpr_of_helperSurfaceClosed spec fields fuel state value hsurface.2]

  private theorem execStmtWithHelpers_eq_execStmt_of_helperSurfaceClosed_mstore
      (spec : CompilationModel)
      (fields : List Field)
      (fuel : Nat)
      (state : RuntimeState)
      (offset value : Expr)
      (hsurface : stmtTouchesUnsupportedHelperSurface (.mstore offset value) = false) :
      execStmtWithHelpers spec fields fuel state (.mstore offset value) =
        execStmtWithEvents fields spec.events state (.mstore offset value) := by
    simp only [stmtTouchesUnsupportedHelperSurface, Bool.or_eq_false_iff] at hsurface
    simp [execStmtWithHelpers, execStmtWithEvents,
      evalExprWithHelpers_eq_evalExpr_of_helperSurfaceClosed spec fields fuel state offset hsurface.1,
      evalExprWithHelpers_eq_evalExpr_of_helperSurfaceClosed spec fields fuel state value hsurface.2]

  private theorem execStmtWithHelpers_eq_execStmt_of_helperSurfaceClosed_tstore
      (spec : CompilationModel)
      (fields : List Field)
      (fuel : Nat)
      (state : RuntimeState)
      (offset value : Expr)
      (hsurface : stmtTouchesUnsupportedHelperSurface (.tstore offset value) = false) :
      execStmtWithHelpers spec fields fuel state (.tstore offset value) =
        execStmtWithEvents fields spec.events state (.tstore offset value) := by
    simp only [stmtTouchesUnsupportedHelperSurface, Bool.or_eq_false_iff] at hsurface
    simp [execStmtWithHelpers, execStmtWithEvents,
      evalExprWithHelpers_eq_evalExpr_of_helperSurfaceClosed spec fields fuel state offset hsurface.1,
      evalExprWithHelpers_eq_evalExpr_of_helperSurfaceClosed spec fields fuel state value hsurface.2]

  private theorem execStmtWithHelpers_eq_execStmt_of_helperSurfaceClosed_calldatacopy
      (spec : CompilationModel)
      (fields : List Field)
      (fuel : Nat)
      (state : RuntimeState)
      (destOffset sourceOffset size : Expr)
      (hsurface :
        stmtTouchesUnsupportedHelperSurface (.calldatacopy destOffset sourceOffset size)
          = false) :
      execStmtWithHelpers spec fields fuel state (.calldatacopy destOffset sourceOffset size) =
        execStmtWithEvents fields spec.events state
          (.calldatacopy destOffset sourceOffset size) := by
    simp only [stmtTouchesUnsupportedHelperSurface, Bool.or_eq_false_iff] at hsurface
    simp [execStmtWithHelpers, execStmtWithEvents,
      evalExprWithHelpers_eq_evalExpr_of_helperSurfaceClosed spec fields fuel state destOffset
        hsurface.1.1,
      evalExprWithHelpers_eq_evalExpr_of_helperSurfaceClosed spec fields fuel state sourceOffset
        hsurface.1.2,
      evalExprWithHelpers_eq_evalExpr_of_helperSurfaceClosed spec fields fuel state size
        hsurface.2]

  private theorem execStmtWithHelpers_eq_execStmt_of_helperSurfaceClosed_returndataCopy
      (spec : CompilationModel)
      (fields : List Field)
      (fuel : Nat)
      (state : RuntimeState)
      (destOffset sourceOffset size : Expr)
      (hsurface :
        stmtTouchesUnsupportedHelperSurface (.returndataCopy destOffset sourceOffset size)
          = false) :
      execStmtWithHelpers spec fields fuel state (.returndataCopy destOffset sourceOffset size) =
        execStmtWithEvents fields spec.events state
          (.returndataCopy destOffset sourceOffset size) := by
    simp only [stmtTouchesUnsupportedHelperSurface, Bool.or_eq_false_iff] at hsurface
    simp [execStmtWithHelpers, execStmtWithEvents,
      evalExprWithHelpers_eq_evalExpr_of_helperSurfaceClosed spec fields fuel state destOffset
        hsurface.1.1,
      evalExprWithHelpers_eq_evalExpr_of_helperSurfaceClosed spec fields fuel state sourceOffset
        hsurface.1.2,
      evalExprWithHelpers_eq_evalExpr_of_helperSurfaceClosed spec fields fuel state size
        hsurface.2]

  private theorem expr_sizeOf_pos (expr : Expr) : 0 < sizeOf expr := by
    cases expr <;> simp

  private theorem stmt_sizeOf_lt_ite_then (cond : Expr) (thenBranch elseBranch : List Stmt) :
      sizeOf thenBranch + 1 < sizeOf (Stmt.ite cond thenBranch elseBranch) := by
    have hcond : 0 < sizeOf cond := expr_sizeOf_pos cond
    simp [Stmt.ite.sizeOf_spec]
    omega

  private theorem stmt_sizeOf_lt_ite_else (cond : Expr) (thenBranch elseBranch : List Stmt) :
      sizeOf elseBranch + 1 < sizeOf (Stmt.ite cond thenBranch elseBranch) := by
    have hcond : 0 < sizeOf cond := expr_sizeOf_pos cond
    simp [Stmt.ite.sizeOf_spec]
    omega

  private theorem stmt_sizeOf_lt_forEach_body
      (varName : String) (count : Expr) (body : List Stmt) :
      sizeOf body + 1 < sizeOf (Stmt.forEach varName count body) := by
    have hcount : 0 < sizeOf count := expr_sizeOf_pos count
    simp [Stmt.forEach.sizeOf_spec]
    omega

  private theorem stmt_sizeOf_lt_forEachSetBit_body
      (varName : String) (bitmap : Expr) (body : List Stmt) :
      sizeOf body + 1 < sizeOf (Stmt.forEachSetBit varName bitmap body) := by
    have hbitmap : 0 < sizeOf bitmap := expr_sizeOf_pos bitmap
    simp [Stmt.forEachSetBit.sizeOf_spec]
    omega

  private theorem stmt_sizeOf_lt_cons (stmt : Stmt) (rest : List Stmt) :
      sizeOf stmt + 1 < sizeOf (stmt :: rest) := by
    cases rest with
    | nil =>
        simp [List.cons.sizeOf_spec]
    | cons head tail =>
        simp [List.cons.sizeOf_spec]
        omega

end -- close the mutual block that started at line 2214

private theorem execStmtListWithHelpers_eq_execStmtList_of_helperSurfaceClosed_inner
    (spec : CompilationModel)
    (fields : List Field)
    (fuel : Nat)
    (state : RuntimeState)
    (stmts : List Stmt)
    (hsurface : stmtListTouchesUnsupportedHelperSurface stmts = false)
    (hstmt : ∀ (st : RuntimeState) (s : Stmt),
      sizeOf s < sizeOf stmts →
      stmtTouchesUnsupportedHelperSurface s = false →
      execStmtWithHelpers spec fields fuel st s =
      execStmtWithEvents fields spec.events st s) :
    execStmtListWithHelpers spec fields fuel state stmts =
      execStmtListWithEvents fields spec.events state stmts := by
  match stmts with
  | [] => simp [execStmtListWithHelpers, execStmtListWithEvents]
  | stmt :: rest =>
      simp only [stmtListTouchesUnsupportedHelperSurface, Bool.or_eq_false_iff] at hsurface
      have hlt : sizeOf stmt < sizeOf (stmt :: rest) := by
        have := stmt_sizeOf_lt_cons stmt rest; omega
      rw [execStmtListWithHelpers,
        hstmt state stmt hlt hsurface.1]
      rw [execStmtListWithEvents]
      cases hexec : execStmtWithEvents fields spec.events state stmt with
      | «continue» next =>
          have hrest_lt : sizeOf rest < sizeOf (stmt :: rest) := by
            simp [List.cons.sizeOf_spec]
          exact execStmtListWithHelpers_eq_execStmtList_of_helperSurfaceClosed_inner
            spec fields fuel next rest hsurface.2
            (fun st s hs hsf => hstmt st s (Nat.lt_trans hs hrest_lt) hsf)
      | stop next => rfl
      | «return» value next => rfl
      | revert => rfl
termination_by sizeOf stmts

private theorem execStmtWithHelpers_eq_execStmt_of_helperSurfaceClosed_aux
    (spec : CompilationModel)
    (fields : List Field)
    (fuel : Nat)
    (state : RuntimeState)
    (stmt : Stmt)
    (hsurface : stmtTouchesUnsupportedHelperSurface stmt = false) :
    execStmtWithHelpers spec fields fuel state stmt =
      execStmtWithEvents fields spec.events state stmt := by
  match stmt with
  | .letVar _ value =>
      simp only [stmtTouchesUnsupportedHelperSurface] at hsurface
      simp [execStmtWithHelpers, execStmtWithEvents,
        evalExprWithHelpers_eq_evalExpr_of_helperSurfaceClosed spec fields fuel state value hsurface]
  | .assignVar _ value =>
      simp only [stmtTouchesUnsupportedHelperSurface] at hsurface
      simp [execStmtWithHelpers, execStmtWithEvents,
        evalExprWithHelpers_eq_evalExpr_of_helperSurfaceClosed spec fields fuel state value hsurface]
  | .setStorage _ value =>
      simp only [stmtTouchesUnsupportedHelperSurface] at hsurface
      simp [execStmtWithHelpers, execStmtWithEvents,
        evalExprWithHelpers_eq_evalExpr_of_helperSurfaceClosed spec fields fuel state value hsurface]
  | .setStorageWord _ _ value =>
      simp only [stmtTouchesUnsupportedHelperSurface] at hsurface
      simp [execStmtWithHelpers, execStmtWithEvents,
        evalExprWithHelpers_eq_evalExpr_of_helperSurfaceClosed spec fields fuel state value hsurface]
  | .setStorageAddr _ value =>
      simp only [stmtTouchesUnsupportedHelperSurface] at hsurface
      simp [execStmtWithHelpers, execStmtWithEvents,
        evalExprWithHelpers_eq_evalExpr_of_helperSurfaceClosed spec fields fuel state value hsurface]
  | .setImmutable _ value =>
      simp only [stmtTouchesUnsupportedHelperSurface] at hsurface
      simp [execStmtWithHelpers, execStmtWithEvents,
        evalExprWithHelpers_eq_evalExpr_of_helperSurfaceClosed spec fields fuel state value hsurface]
  | .storageArrayPush _ value =>
      simp only [stmtTouchesUnsupportedHelperSurface] at hsurface
      simp [execStmtWithHelpers, execStmtWithEvents,
        evalExprWithHelpers_eq_evalExpr_of_helperSurfaceClosed spec fields fuel state value hsurface]
  | .require cond _ =>
      simp only [stmtTouchesUnsupportedHelperSurface] at hsurface
      simp [execStmtWithHelpers, execStmtWithEvents,
        evalExprWithHelpers_eq_evalExpr_of_helperSurfaceClosed spec fields fuel state cond hsurface]
  | .return value =>
      simp only [stmtTouchesUnsupportedHelperSurface] at hsurface
      simp [execStmtWithHelpers, execStmtWithEvents,
        evalExprWithHelpers_eq_evalExpr_of_helperSurfaceClosed spec fields fuel state value hsurface]
  | .stop =>
      simp [execStmtWithHelpers, execStmtWithEvents]
  | .setMapping fieldName key value =>
      exact execStmtWithHelpers_eq_execStmt_of_helperSurfaceClosed_setMapping
        spec fields fuel state fieldName key value hsurface
  | .setMappingWord fieldName key wordOffset value =>
      exact execStmtWithHelpers_eq_execStmt_of_helperSurfaceClosed_setMappingWord
        spec fields fuel state fieldName key value wordOffset hsurface
  | .setMappingPackedWord fieldName key wordOffset packed value =>
      exact execStmtWithHelpers_eq_execStmt_of_helperSurfaceClosed_setMappingPackedWord
        spec fields fuel state fieldName key value wordOffset packed hsurface
  | .setMappingUint fieldName key value =>
      exact execStmtWithHelpers_eq_execStmt_of_helperSurfaceClosed_setMappingUint
        spec fields fuel state fieldName key value hsurface
  | .setStructMember fieldName key memberName value =>
      exact execStmtWithHelpers_eq_execStmt_of_helperSurfaceClosed_setStructMember
        spec fields fuel state fieldName memberName key value hsurface
  | .setMapping2 fieldName key1 key2 value =>
      exact execStmtWithHelpers_eq_execStmt_of_helperSurfaceClosed_setMapping2
        spec fields fuel state fieldName key1 key2 value hsurface
  | .setMapping2Word fieldName key1 key2 wordOffset value =>
      exact execStmtWithHelpers_eq_execStmt_of_helperSurfaceClosed_setMapping2Word
        spec fields fuel state fieldName key1 key2 value wordOffset hsurface
  | .setStructMember2 fieldName key1 key2 memberName value =>
      exact execStmtWithHelpers_eq_execStmt_of_helperSurfaceClosed_setStructMember2
        spec fields fuel state fieldName memberName key1 key2 value hsurface
  | .setStorageArrayElement fieldName index value =>
      exact execStmtWithHelpers_eq_execStmt_of_helperSurfaceClosed_setStorageArrayElement
        spec fields fuel state fieldName index value hsurface
  | .mstore offset value =>
      exact execStmtWithHelpers_eq_execStmt_of_helperSurfaceClosed_mstore
        spec fields fuel state offset value hsurface
  | .tstore offset value =>
      exact execStmtWithHelpers_eq_execStmt_of_helperSurfaceClosed_tstore
        spec fields fuel state offset value hsurface
  | .ite cond thenBranch elseBranch =>
      simp only [stmtTouchesUnsupportedHelperSurface, Bool.or_eq_false_iff] at hsurface
      rcases hsurface with ⟨⟨hcondSurface, hthenSurface⟩, helseSurface⟩
      simp only [execStmtWithHelpers, execStmtWithEvents,
        evalExprWithHelpers_eq_evalExpr_of_helperSurfaceClosed spec fields fuel state cond hcondSurface]
      cases evalExpr fields state cond with
      | none => rfl
      | some resolved =>
          by_cases hcond : resolved != 0
          · simp [hcond]
            exact execStmtListWithHelpers_eq_execStmtList_of_helperSurfaceClosed_inner
              spec fields fuel state thenBranch hthenSurface
              (fun st s hs hsf =>
                have : sizeOf s < sizeOf (Stmt.ite cond thenBranch elseBranch) := by
                  have := stmt_sizeOf_lt_ite_then cond thenBranch elseBranch; omega
                execStmtWithHelpers_eq_execStmt_of_helperSurfaceClosed_aux
                  spec fields fuel st s hsf)
          · simp [hcond]
            exact execStmtListWithHelpers_eq_execStmtList_of_helperSurfaceClosed_inner
              spec fields fuel state elseBranch helseSurface
              (fun st s hs hsf =>
                have : sizeOf s < sizeOf (Stmt.ite cond thenBranch elseBranch) := by
                  have := stmt_sizeOf_lt_ite_else cond thenBranch elseBranch; omega
                execStmtWithHelpers_eq_execStmt_of_helperSurfaceClosed_aux
                  spec fields fuel st s hsf)
  | .setMappingChain fieldName keys value =>
      exact execStmtWithHelpers_eq_execStmt_of_helperSurfaceClosed_keyListValue
        spec fields fuel state fieldName keys value hsurface
  | .internalCall _ _ => cases hsurface
  | .internalCallAssign _ _ _ => cases hsurface
  | .storageArrayPop _ => simp [execStmtWithHelpers, execStmtWithEvents]
  | .requireError cond _ args =>
      simp only [stmtTouchesUnsupportedHelperSurface, Bool.or_eq_false_iff] at hsurface
      simp [execStmtWithHelpers, execStmtWithEvents, typedErrorRevertResult,
        evalExprWithHelpers_eq_evalExpr_of_helperSurfaceClosed spec fields fuel state cond hsurface.1]
  | .revertError _ args =>
      simp [execStmtWithHelpers, execStmtWithEvents, typedErrorRevertResult]
  | .panicCode _ => simp [execStmtWithHelpers, execStmtWithEvents]
  | .returnValues _ => simp [execStmtWithHelpers, execStmtWithEvents]
  | .returnArray _ => simp [execStmtWithHelpers, execStmtWithEvents]
  | .returnBytes _ => simp [execStmtWithHelpers, execStmtWithEvents]
  | .returnStorageWords _ => simp [execStmtWithHelpers, execStmtWithEvents]
  | .returnCodeData _ => simp [execStmtWithHelpers, execStmtWithEvents]
  | .calldatacopy destOffset sourceOffset size =>
      exact execStmtWithHelpers_eq_execStmt_of_helperSurfaceClosed_calldatacopy
        spec fields fuel state destOffset sourceOffset size hsurface
  | .returndataCopy destOffset sourceOffset size =>
      exact execStmtWithHelpers_eq_execStmt_of_helperSurfaceClosed_returndataCopy
        spec fields fuel state destOffset sourceOffset size hsurface
  | .revertReturndata => simp [execStmtWithHelpers, execStmtWithEvents]
  | .emit _ args =>
      simp only [stmtTouchesUnsupportedHelperSurface] at hsurface
      have hall : args.all (fun expr => exprTouchesUnsupportedHelperSurface expr == false) = true := by
        induction args with
        | nil => simp
        | cons expr rest ih =>
          simp only [exprListTouchesUnsupportedHelperSurface, Bool.or_eq_false_iff] at hsurface
          simp only [List.all_cons, Bool.and_eq_true, beq_iff_eq]
          exact ⟨hsurface.1, ih hsurface.2⟩
      simp [execStmtWithHelpers, execStmtWithEvents,
        evalExprListWithHelpers_eq_evalExprList_of_helperSurfaceClosed spec fields fuel state args hall,
        evalExprList_eq_mapM]
  | .rawLog _ _ _ => simp [execStmtWithHelpers, execStmtWithEvents]
  | .unsafeYul _ => cases hsurface
  | .externalCallBind _ _ args =>
      simp only [stmtTouchesUnsupportedHelperSurface] at hsurface
      have hall : args.all (fun expr => exprTouchesUnsupportedHelperSurface expr == false) = true := by
        induction args with
        | nil => simp
        | cons expr rest ih =>
          simp only [exprListTouchesUnsupportedHelperSurface, Bool.or_eq_false_iff] at hsurface
          simp only [List.all_cons, Bool.and_eq_true, beq_iff_eq]
          exact ⟨hsurface.1, ih hsurface.2⟩
      simp [execStmtWithHelpers, execStmtWithEvents,
        evalExprListWithHelpers_eq_evalExprList_of_helperSurfaceClosed spec fields fuel state args hall,
        evalExprList_eq_mapM]
  | .tryExternalCallBind _ _ _ args =>
      simp only [stmtTouchesUnsupportedHelperSurface] at hsurface
      have hall : args.all (fun expr => exprTouchesUnsupportedHelperSurface expr == false) = true := by
        induction args with
        | nil => simp
        | cons expr rest ih =>
          simp only [exprListTouchesUnsupportedHelperSurface, Bool.or_eq_false_iff] at hsurface
          simp only [List.all_cons, Bool.and_eq_true, beq_iff_eq]
          exact ⟨hsurface.1, ih hsurface.2⟩
      simp [execStmtWithHelpers, execStmtWithEvents,
        evalExprListWithHelpers_eq_evalExprList_of_helperSurfaceClosed spec fields fuel state args hall,
        evalExprList_eq_mapM]
  | .ecm _ args =>
      simp only [stmtTouchesUnsupportedHelperSurface] at hsurface
      have hall : args.all (fun expr => exprTouchesUnsupportedHelperSurface expr == false) = true := by
        induction args with
        | nil => simp
        | cons expr rest ih =>
          simp only [exprListTouchesUnsupportedHelperSurface, Bool.or_eq_false_iff] at hsurface
          simp only [List.all_cons, Bool.and_eq_true, beq_iff_eq]
          exact ⟨hsurface.1, ih hsurface.2⟩
      simp [execStmtWithHelpers, execStmtWithEvents,
        evalExprListWithHelpers_eq_evalExprList_of_helperSurfaceClosed spec fields fuel state args hall,
        evalExprList_eq_mapM]
  | .forEach _ _ _ =>
      simp only [stmtTouchesUnsupportedHelperSurface, Bool.or_eq_false_iff] at hsurface
      rename_i varName count body
      have hcount :=
        evalExprWithHelpers_eq_evalExpr_of_helperSurfaceClosed
          spec fields fuel state count hsurface.1
      simp only [execStmtWithHelpers, execStmtWithEvents, hcount]
      cases evalExpr fields state count with
      | none => rfl
      | some bound =>
          let initialLoopState :=
            { state with bindings := bindValue state.bindings varName (wordNormalize 0) }
          exact execForEachLoop_congr
            (varName := varName)
            (runBodyA := fun loopState =>
              execStmtListWithHelpers spec fields fuel loopState body)
            (runBodyB := fun loopState =>
              execStmtListWithEvents fields spec.events loopState body)
            (fun loopState =>
              execStmtListWithHelpers_eq_execStmtList_of_helperSurfaceClosed_inner
                spec fields fuel loopState body hsurface.2
                (fun st s hs hsf =>
                  have : sizeOf s < sizeOf (Stmt.forEach varName count body) := by
                    have hbody := stmt_sizeOf_lt_forEach_body varName count body
                    omega
                  execStmtWithHelpers_eq_execStmt_of_helperSurfaceClosed_aux
                    spec fields fuel st s hsf))
            initialLoopState 0 bound
  | .forEachSetBit _ _ _ =>
      simp only [stmtTouchesUnsupportedHelperSurface, Bool.or_eq_false_iff] at hsurface
      rename_i varName bitmap body
      have hbitmap :=
        evalExprWithHelpers_eq_evalExpr_of_helperSurfaceClosed
          spec fields fuel state bitmap hsurface.1
      simp only [execStmtWithHelpers, execStmtWithEvents, hbitmap]
      cases evalExpr fields state bitmap with
      | none => rfl
      | some bits =>
          exact execForEachSetBitLoop_congr
            (varName := varName)
            (runBodyA := fun loopState =>
              execStmtListWithHelpers spec fields fuel loopState body)
            (runBodyB := fun loopState =>
              execStmtListWithEvents fields spec.events loopState body)
            (fun loopState =>
              execStmtListWithHelpers_eq_execStmtList_of_helperSurfaceClosed_inner
                spec fields fuel loopState body hsurface.2
                (fun st s hs hsf =>
                  have : sizeOf s < sizeOf (Stmt.forEachSetBit varName bitmap body) := by
                    have hbody := stmt_sizeOf_lt_forEachSetBit_body varName bitmap body
                    omega
                  execStmtWithHelpers_eq_execStmt_of_helperSurfaceClosed_aux
                    spec fields fuel st s hsf))
            256 state bits
termination_by sizeOf stmt

theorem execStmtWithHelpers_eq_execStmt_of_helperSurfaceClosed
    (spec : CompilationModel)
    (fields : List Field)
    (fuel : Nat)
    (state : RuntimeState)
    (stmt : Stmt)
    (hsurface : stmtTouchesUnsupportedHelperSurface stmt = false) :
    execStmtWithHelpers spec fields fuel state stmt =
      execStmtWithEvents fields spec.events state stmt := by
  exact execStmtWithHelpers_eq_execStmt_of_helperSurfaceClosed_aux
    spec fields fuel state stmt hsurface

theorem execStmtListWithHelpers_eq_execStmtList_of_helperSurfaceClosed
    (spec : CompilationModel)
    (fields : List Field)
    (fuel : Nat)
    (state : RuntimeState)
    (stmts : List Stmt)
    (hsurface : stmtListTouchesUnsupportedHelperSurface stmts = false) :
    execStmtListWithHelpers spec fields fuel state stmts =
      execStmtListWithEvents fields spec.events state stmts := by
  exact execStmtListWithHelpers_eq_execStmtList_of_helperSurfaceClosed_inner
    spec fields fuel state stmts hsurface
    (fun st s _ hsf => execStmtWithHelpers_eq_execStmt_of_helperSurfaceClosed_aux
      spec fields fuel st s hsf)

/-- Exact source-side helper-composition target for a statement list: the
helper-aware source semantics should conservatively extend the legacy
helper-free semantics on the given runtime state. Future helper-summary/rank
consumption should target this proposition directly rather than the temporary
syntactic helper-surface gate. -/
def ExecStmtListWithHelpersConservativeExtensionGoal
    (spec : CompilationModel)
    (fields : List Field)
    (fuel : Nat)
    (state : RuntimeState)
    (stmts : List Stmt) : Prop :=
  execStmtListWithHelpers spec fields fuel state stmts =
    execStmtListWithEvents fields spec.events state stmts

theorem execStmtListWithHelpersConservativeExtensionGoal_of_helperSurfaceClosed
    (spec : CompilationModel)
    (fields : List Field)
    (fuel : Nat)
    (state : RuntimeState)
    (stmts : List Stmt)
    (hsurface : stmtListTouchesUnsupportedHelperSurface stmts = false) :
    ExecStmtListWithHelpersConservativeExtensionGoal spec fields fuel state stmts :=
  execStmtListWithHelpers_eq_execStmtList_of_helperSurfaceClosed
    (spec := spec)
    (fields := fields)
    (fuel := fuel)
    (state := state)
    (stmts := stmts)
    hsurface

theorem interpretFunctionWithHelpers_eq_interpretFunction_of_helperSurfaceClosed
    (spec : CompilationModel)
    (fuel : Nat)
    (fn : FunctionSpec)
    (tx : IRTransaction)
    (initialWorld : Verity.ContractState)
    (hsurface : stmtListTouchesUnsupportedHelperSurface fn.body = false) :
    interpretFunctionWithHelpers spec fuel fn tx initialWorld =
      interpretFunction spec fn tx initialWorld := by
  unfold interpretFunctionWithHelpers interpretFunction
  simp only
  cases hbind : bindExternalParams tx.functionSelector fn.params tx.args with
  | none =>
      simp
  | some bindings =>
      have hbody :
          execStmtListWithHelpers spec (effectiveFields spec) fuel
            { world := withTransactionContext initialWorld tx, bindings := bindings, selector := tx.functionSelector } fn.body =
          execStmtListWithEvents (effectiveFields spec) spec.events
            { world := withTransactionContext initialWorld tx, bindings := bindings, selector := tx.functionSelector } fn.body :=
        execStmtListWithHelpers_eq_execStmtList_of_helperSurfaceClosed
          (spec := spec)
          (fields := effectiveFields spec)
          (fuel := fuel)
          (state := { world := withTransactionContext initialWorld tx, bindings := bindings, selector := tx.functionSelector })
          (stmts := fn.body)
          hsurface
      simp [hbody]

private theorem mem_of_find?_some_local
    {α : Type} (p : α → Bool) :
    ∀ {xs : List α} {x : α}, List.find? p xs = some x → x ∈ xs
  | [], _, h => by
      simp at h
  | y :: ys, x, h => by
      by_cases hp : p y
      · simp [List.find?, hp] at h
        cases h
        simp
      · simp [List.find?, hp] at h
        exact List.mem_cons.2 (Or.inr (mem_of_find?_some_local p h))

private theorem mem_left_of_mem_zip_local
    {α β : Type} :
    ∀ {xs : List α} {ys : List β} {x : α} {y : β}, (x, y) ∈ xs.zip ys → x ∈ xs
  | [], _, _, _, h => by
      simp at h
  | _ :: _, [], _, _, h => by
      simp at h
  | x0 :: xs, y0 :: ys, x, y, h => by
      simp [List.zip] at h ⊢
      rcases h with h | h
      · rcases h with ⟨rfl, rfl⟩
        simp
      · exact Or.inr (mem_left_of_mem_zip_local h)

theorem findFunctionBySelector_mem_selectorDispatchedFunctions
    {spec : CompilationModel}
    {selectors : List Nat}
    {selector : Nat}
    {fn : FunctionSpec}
    (hfind : findFunctionBySelector spec selectors selector = some fn) :
    fn ∈ selectorDispatchedFunctions spec := by
  unfold findFunctionBySelector at hfind
  rcases hentry :
      List.find? (fun entry => entry.2 == selector) (selectorFunctionPairs spec selectors) with
    (_ | entry) <;> simp [hentry] at hfind
  cases entry with
  | mk foundFn foundSelector =>
      cases hfind
      have hmem :
          (foundFn, foundSelector) ∈ (selectorDispatchedFunctions spec).zip selectors := by
        simpa [selectorFunctionPairs] using
          mem_of_find?_some_local (fun entry => entry.2 == selector) hentry
      exact mem_left_of_mem_zip_local hmem

theorem interpretContractWithHelpers_eq_interpretContract_of_supportedSpec
    {spec : CompilationModel}
    {selectors : List Nat}
    (hSupported : SupportedSpec spec selectors)
    (fuel : Nat)
    (tx : IRTransaction)
    (initialWorld : Verity.ContractState) :
    interpretContractWithHelpers spec selectors fuel tx initialWorld =
      interpretContract spec selectors tx initialWorld := by
  unfold interpretContractWithHelpers interpretContract
  split
  · rename_i fn hfind
    have hfn : fn ∈ selectorDispatchedFunctions spec :=
      findFunctionBySelector_mem_selectorDispatchedFunctions hfind
    have hfnModel : fn ∈ spec.functions := List.mem_of_mem_filter hfn
    split
    · rfl
    · exact interpretFunctionWithHelpers_eq_interpretFunction_of_helperSurfaceClosed
        (spec := spec)
        (fuel := fuel)
        (fn := fn)
        (tx := tx)
        (initialWorld := initialWorld)
        (hSupported.supportedFunctionOfSelectorDispatched hfn).body.helperSurfaceClosed
  · rfl

theorem interpretContractWithHelpers_eq_interpretContract_of_supportedSpecExceptMappingWrites
    {spec : CompilationModel}
    {selectors : List Nat}
    (hSupported : SupportedSpecExceptMappingWrites spec selectors)
    (fuel : Nat)
    (tx : IRTransaction)
    (initialWorld : Verity.ContractState) :
    interpretContractWithHelpers spec selectors fuel tx initialWorld =
      interpretContract spec selectors tx initialWorld := by
  unfold interpretContractWithHelpers interpretContract
  split
  · rename_i fn hfind
    have hfn : fn ∈ selectorDispatchedFunctions spec :=
      findFunctionBySelector_mem_selectorDispatchedFunctions hfind
    split
    · rfl
    · exact interpretFunctionWithHelpers_eq_interpretFunction_of_helperSurfaceClosed
        (spec := spec)
        (fuel := fuel)
        (fn := fn)
        (tx := tx)
        (initialWorld := initialWorld)
        (hSupported.supportedFunctionOfSelectorDispatched hfn).body.helperSurfaceClosed
  · rfl

theorem interpretContractWithHelpers_eq_interpretContract_of_supportedSpecWithScalarEvents
    {spec : CompilationModel}
    {selectors : List Nat}
    (hSupported : SupportedSpecWithScalarEvents spec selectors)
    (fuel : Nat)
    (tx : IRTransaction)
    (initialWorld : Verity.ContractState) :
    interpretContractWithHelpers spec selectors fuel tx initialWorld =
      interpretContract spec selectors tx initialWorld := by
  unfold interpretContractWithHelpers interpretContract
  split
  · rename_i fn hfind
    have hfn : fn ∈ selectorDispatchedFunctions spec :=
      findFunctionBySelector_mem_selectorDispatchedFunctions hfind
    split
    · rfl
    · exact interpretFunctionWithHelpers_eq_interpretFunction_of_helperSurfaceClosed
        (spec := spec)
        (fuel := fuel)
        (fn := fn)
        (tx := tx)
        (initialWorld := initialWorld)
        (hSupported.supportedFunctionOfSelectorDispatched hfn).body.helperSurfaceClosed
  · rfl

end SourceSemantics

/-- Whole-contract source-side semantics for the first generic Layer 2 fragment.
The observable result intentionally mirrors `interpretIR`: selector dispatch,
scalar parameter decoding, success/revert, rollback on revert, return value,
and encoded storage/event observations. -/
def sourceContractSemantics (spec : CompilationModel) (selectors : List Nat)
    (tx : IRTransaction) (initialWorld : Verity.ContractState) :
    SourceSemantics.SourceContractResult :=
  SourceSemantics.interpretContract spec selectors tx initialWorld

noncomputable def sourceContractSemanticsWithHelpers (spec : CompilationModel) (selectors : List Nat)
    (fuel : Nat)
    (tx : IRTransaction) (initialWorld : Verity.ContractState) :
    SourceSemantics.SourceContractResult :=
  SourceSemantics.interpretContractWithHelpers spec selectors fuel tx initialWorld

noncomputable def supportedSourceFunctionSemantics
    (spec : CompilationModel)
    (selectors : List Nat)
    (hSupported : SupportedSpec spec selectors)
    (fn : FunctionSpec)
    (tx : IRTransaction)
    (initialWorld : Verity.ContractState) :
    SourceSemantics.SourceContractResult :=
  SourceSemantics.interpretFunctionWithHelpers
    spec hSupported.helperFuel fn tx initialWorld

noncomputable def supportedSourceFunctionSemanticsWithHelpers
    (spec : CompilationModel)
    (selectors : List Nat)
    (hSupported : SupportedSpecWithHelpers spec selectors)
    (fn : FunctionSpec)
    (tx : IRTransaction)
    (initialWorld : Verity.ContractState) :
    SourceSemantics.SourceContractResult :=
  SourceSemantics.interpretFunctionWithHelpers
    spec hSupported.helperFuel fn tx initialWorld

noncomputable def supportedSourceFunctionSemanticsExceptMappingWrites
    (spec : CompilationModel)
    (selectors : List Nat)
    (hSupported : SupportedSpecExceptMappingWrites spec selectors)
    (fn : FunctionSpec)
    (tx : IRTransaction)
    (initialWorld : Verity.ContractState) :
    SourceSemantics.SourceContractResult :=
  SourceSemantics.interpretFunctionWithHelpers
    spec hSupported.helperFuel fn tx initialWorld

noncomputable def supportedSourceFunctionSemanticsWithScalarEvents
    (spec : CompilationModel)
    (selectors : List Nat)
    (hSupported : SupportedSpecWithScalarEvents spec selectors)
    (fn : FunctionSpec)
    (tx : IRTransaction)
    (initialWorld : Verity.ContractState) :
    SourceSemantics.SourceContractResult :=
  SourceSemantics.interpretFunctionWithHelpers
    spec hSupported.helperFuel fn tx initialWorld

noncomputable def supportedSourceContractSemantics
    (spec : CompilationModel)
    (selectors : List Nat)
    (hSupported : SupportedSpec spec selectors)
    (tx : IRTransaction)
    (initialWorld : Verity.ContractState) :
  SourceSemantics.SourceContractResult :=
  sourceContractSemanticsWithHelpers spec selectors hSupported.helperFuel tx initialWorld

noncomputable def supportedSourceContractSemanticsWithHelpers
    (spec : CompilationModel)
    (selectors : List Nat)
    (hSupported : SupportedSpecWithHelpers spec selectors)
    (tx : IRTransaction)
    (initialWorld : Verity.ContractState) :
    SourceSemantics.SourceContractResult :=
  sourceContractSemanticsWithHelpers spec selectors hSupported.helperFuel tx initialWorld

noncomputable def supportedSourceContractSemanticsWithScalarEvents
    (spec : CompilationModel)
    (selectors : List Nat)
    (hSupported : SupportedSpecWithScalarEvents spec selectors)
    (tx : IRTransaction)
    (initialWorld : Verity.ContractState) :
    SourceSemantics.SourceContractResult :=
  sourceContractSemanticsWithHelpers spec selectors hSupported.helperFuel tx initialWorld

noncomputable def supportedSourceContractSemanticsExceptMappingWrites
    (spec : CompilationModel)
    (selectors : List Nat)
    (hSupported : SupportedSpecExceptMappingWrites spec selectors)
    (tx : IRTransaction)
    (initialWorld : Verity.ContractState) :
    SourceSemantics.SourceContractResult :=
  sourceContractSemanticsWithHelpers spec selectors hSupported.helperFuel tx initialWorld

theorem sourceContractSemanticsWithHelpers_eq_sourceContractSemantics_of_supportedSpec
    {spec : CompilationModel}
    {selectors : List Nat}
    (hSupported : SupportedSpec spec selectors)
    (fuel : Nat)
    (tx : IRTransaction)
    (initialWorld : Verity.ContractState) :
    sourceContractSemanticsWithHelpers spec selectors fuel tx initialWorld =
      sourceContractSemantics spec selectors tx initialWorld := by
  simpa [sourceContractSemanticsWithHelpers, sourceContractSemantics] using
    SourceSemantics.interpretContractWithHelpers_eq_interpretContract_of_supportedSpec
      hSupported fuel tx initialWorld

theorem sourceContractSemanticsWithHelpers_eq_sourceContractSemantics_of_supportedSpecExceptMappingWrites
    {spec : CompilationModel}
    {selectors : List Nat}
    (hSupported : SupportedSpecExceptMappingWrites spec selectors)
    (fuel : Nat)
    (tx : IRTransaction)
    (initialWorld : Verity.ContractState) :
    sourceContractSemanticsWithHelpers spec selectors fuel tx initialWorld =
      sourceContractSemantics spec selectors tx initialWorld := by
  simpa [sourceContractSemanticsWithHelpers, sourceContractSemantics] using
    SourceSemantics.interpretContractWithHelpers_eq_interpretContract_of_supportedSpecExceptMappingWrites
      hSupported fuel tx initialWorld

theorem sourceContractSemanticsWithHelpers_eq_sourceContractSemantics_of_supportedSpecWithScalarEvents
    {spec : CompilationModel}
    {selectors : List Nat}
    (hSupported : SupportedSpecWithScalarEvents spec selectors)
    (fuel : Nat)
    (tx : IRTransaction)
    (initialWorld : Verity.ContractState) :
    sourceContractSemanticsWithHelpers spec selectors fuel tx initialWorld =
      sourceContractSemantics spec selectors tx initialWorld := by
  simpa [sourceContractSemanticsWithHelpers, sourceContractSemantics] using
    SourceSemantics.interpretContractWithHelpers_eq_interpretContract_of_supportedSpecWithScalarEvents
      hSupported fuel tx initialWorld

theorem supportedSourceFunctionSemantics_eq_interpretFunction_of_selectorDispatched
    {spec : CompilationModel}
    {selectors : List Nat}
    (hSupported : SupportedSpec spec selectors)
    {fn : FunctionSpec}
    (hfn : fn ∈ selectorDispatchedFunctions spec)
    (tx : IRTransaction)
    (initialWorld : Verity.ContractState) :
    supportedSourceFunctionSemantics spec selectors hSupported fn tx initialWorld =
      SourceSemantics.interpretFunction spec fn tx initialWorld := by
  simpa [supportedSourceFunctionSemantics] using
    SourceSemantics.interpretFunctionWithHelpers_eq_interpretFunction_of_helperSurfaceClosed
      (spec := spec)
      (fuel := hSupported.helperFuel)
      (fn := fn)
      (tx := tx)
      (initialWorld := initialWorld)
      (hSupported.supportedFunctionOfSelectorDispatched hfn).body.helperSurfaceClosed

theorem supportedSourceFunctionSemanticsWithScalarEvents_eq_interpretFunction_of_selectorDispatched
    {spec : CompilationModel}
    {selectors : List Nat}
    (hSupported : SupportedSpecWithScalarEvents spec selectors)
    {fn : FunctionSpec}
    (hfn : fn ∈ selectorDispatchedFunctions spec)
    (tx : IRTransaction)
    (initialWorld : Verity.ContractState) :
    supportedSourceFunctionSemanticsWithScalarEvents spec selectors hSupported fn tx initialWorld =
      SourceSemantics.interpretFunction spec fn tx initialWorld := by
  simpa [supportedSourceFunctionSemanticsWithScalarEvents] using
    SourceSemantics.interpretFunctionWithHelpers_eq_interpretFunction_of_helperSurfaceClosed
      (spec := spec)
      (fuel := hSupported.helperFuel)
      (fn := fn)
      (tx := tx)
      (initialWorld := initialWorld)
      (hSupported.supportedFunctionOfSelectorDispatched hfn).body.helperSurfaceClosed

theorem supportedSourceFunctionSemanticsExceptMappingWrites_eq_interpretFunction_of_selectorDispatched
    {spec : CompilationModel}
    {selectors : List Nat}
    (hSupported : SupportedSpecExceptMappingWrites spec selectors)
    {fn : FunctionSpec}
    (hfn : fn ∈ selectorDispatchedFunctions spec)
    (tx : IRTransaction)
    (initialWorld : Verity.ContractState) :
    supportedSourceFunctionSemanticsExceptMappingWrites spec selectors hSupported fn tx initialWorld =
      SourceSemantics.interpretFunction spec fn tx initialWorld := by
  simpa [supportedSourceFunctionSemanticsExceptMappingWrites] using
    SourceSemantics.interpretFunctionWithHelpers_eq_interpretFunction_of_helperSurfaceClosed
      (spec := spec)
      (fuel := hSupported.helperFuel)
      (fn := fn)
      (tx := tx)
      (initialWorld := initialWorld)
      (hSupported.supportedFunctionOfSelectorDispatched hfn).body.helperSurfaceClosed

theorem supportedSourceContractSemantics_eq_sourceContractSemantics
    {spec : CompilationModel}
    {selectors : List Nat}
    (hSupported : SupportedSpec spec selectors)
    (tx : IRTransaction)
    (initialWorld : Verity.ContractState) :
    supportedSourceContractSemantics spec selectors hSupported tx initialWorld =
      sourceContractSemantics spec selectors tx initialWorld := by
  exact sourceContractSemanticsWithHelpers_eq_sourceContractSemantics_of_supportedSpec
    hSupported hSupported.helperFuel tx initialWorld

theorem supportedSourceContractSemanticsWithScalarEvents_eq_sourceContractSemantics
    {spec : CompilationModel}
    {selectors : List Nat}
    (hSupported : SupportedSpecWithScalarEvents spec selectors)
    (tx : IRTransaction)
    (initialWorld : Verity.ContractState) :
    supportedSourceContractSemanticsWithScalarEvents spec selectors hSupported tx initialWorld =
      sourceContractSemantics spec selectors tx initialWorld := by
  exact sourceContractSemanticsWithHelpers_eq_sourceContractSemantics_of_supportedSpecWithScalarEvents
    hSupported hSupported.helperFuel tx initialWorld

theorem supportedSourceContractSemanticsExceptMappingWrites_eq_sourceContractSemantics
    {spec : CompilationModel}
    {selectors : List Nat}
    (hSupported : SupportedSpecExceptMappingWrites spec selectors)
    (tx : IRTransaction)
    (initialWorld : Verity.ContractState) :
    supportedSourceContractSemanticsExceptMappingWrites spec selectors hSupported tx initialWorld =
      sourceContractSemantics spec selectors tx initialWorld := by
  exact sourceContractSemanticsWithHelpers_eq_sourceContractSemantics_of_supportedSpecExceptMappingWrites
    hSupported hSupported.helperFuel tx initialWorld

-- Concrete executable smoke checks for these semantics live in
-- `SourceSemanticsFeatureTest.lean`, where runtime normalization is allowed
-- without making the proof/audit import path depend on large `decide` reductions.

private def storageArraySourceSpec : CompilationModel :=
  { name := "StorageArraySource"
    fields := [{ name := "queue", ty := .dynamicArray .uint256, «slot» := some 7 }]
    constructor := none
    functions :=
      [ { name := "length"
          params := []
          returnType := some .uint256
          body := [Stmt.return (Expr.storageArrayLength "queue")] }
      , { name := "first"
          params := []
          returnType := some .uint256
          body := [Stmt.return (Expr.storageArrayElement "queue" (.literal 0))] }
      , { name := "push"
          params := [{ name := "value", ty := .uint256 }]
          returnType := none
          body := [Stmt.storageArrayPush "queue" (.param "value"), .stop] }
      , { name := "write0"
          params := [{ name := "value", ty := .uint256 }]
          returnType := none
          body := [Stmt.setStorageArrayElement "queue" (.literal 0) (.param "value"), .stop] }
      , { name := "pop"
          params := []
          returnType := none
          body := [Stmt.storageArrayPop "queue", .stop] } ] }

private def storageArrayInitialWorld : Verity.ContractState :=
  Verity.defaultState.writeArray 7 [11, 17]

end Compiler.Proofs.IRGeneration
