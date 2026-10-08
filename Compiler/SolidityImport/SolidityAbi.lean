import Verity.Core.Model.DynamicAbi

/-! Source ABI primitives for the dynamic-struct importer under development.
These operate on complete calldata words plus a selector. They are not yet
wired to parameter lowering, and do not claim partial-byte calldata support. -/
namespace Compiler.CompilationModel.SolidityImport.SolidityAbi

private def modulus : Nat := 2^256
private def word (value : Nat) : Nat := value % modulus

def byteAt (selector : Nat) (calldata : List Nat) (offset : Nat) : Nat :=
  if offset < 4 then
    (selector % 2^32) / 2^(8*(3-offset)) % 256
  else
    let position := offset - 4
    word (calldata.getD (position / 32) 0) / 2^(8*(31-position % 32)) % 256

/-- The start offset is an EVM word; subsequent bytes do not wrap around the
address space. In particular, a load at 2^256-1 cannot read the selector. -/
def loadWord (selector : Nat) (calldata : List Nat) (offset : Nat) : Nat :=
  (List.range 32).foldl (fun acc index => acc * 256 + byteAt selector calldata (word offset + index)) 0

def signedWord (value : Nat) : Int :=
  let normalized := word value
  if normalized < 2^255 then Int.ofNat normalized
  else Int.ofNat normalized - Int.ofNat modulus

private def subWord (left right : Nat) : Nat := word (word left + modulus - word right)
def calldataSize (calldata : List Nat) : Nat := 4 + 32 * calldata.length

/-- solc's top-level dynamic-tuple head bounds, including the complete root
parameter head. Root offsets are uint64-bounded but may overlap or misalign. -/
def tupleHead? (selector : Nat) (calldata : List Nat)
    (rootHeadWords parameterIndex tupleHeadWords : Nat) : Option Nat := do
  if parameterIndex ≥ rootHeadWords ∨ calldataSize calldata < 4 + 32*rootHeadWords then none
  else
    let relative := loadWord selector calldata (4 + 32*parameterIndex)
    if relative ≤ 2^64-1 ∧ 4 + relative + 32*tupleHeadWords ≤ calldataSize calldata then
      some (4 + relative)
    else none

structure ArrayView where
  dataOffset : Nat
  length : Nat
  deriving Repr, DecidableEq

/-- The lazy calldata rule for an array of statically sized elements. This
mirrors solc's signed checks and modular arithmetic; requiring an unsigned
forward offset would incorrectly reject the measured backwards-offset case.
Malformed decoding remains `none`, distinct from the later index panic. -/
def staticArrayView? (selector : Nat) (calldata : List Nat)
    (tupleHead memberWord elementWords : Nat) : Option ArrayView := do
  let relative := loadWord selector calldata (word (tupleHead + 32*memberWord))
  let available := subWord (subWord (calldataSize calldata) tupleHead) 31
  if signedWord relative ≥ signedWord available then none
  else
    let address := word (tupleHead + relative)
    let length := loadWord selector calldata address
    if length > 2^64-1 then none
    else
      let start := word (address + 32)
      let lastStart := subWord (calldataSize calldata) (word (32*elementWords*length))
      if signedWord start > signedWord lastStart then none
      else some ⟨start, length⟩

inductive DecodeFailure where
  | malformed
  | allocation
  deriving Repr, DecidableEq

/-- Allocate a word-aligned memory region with solc's uint64 free-pointer
limit. Allocation failure must eventually become Panic(0x41), not an empty
ABI revert. This helper does not write the allocated memory. -/
def allocateWords (freePointer words : Nat) : Except DecodeFailure Nat :=
  let next := word (freePointer + word (32*words))
  if next > 2^64-1 ∨ next < freePointer then .error .allocation
  else .ok next

/-- Decode the header of a memory array of static elements, in source order:
offset/length-word availability, allocation, then complete payload bounds.
The returned free pointer accounts for the array of element references;
decoding and allocating each struct element remain the caller's obligations. -/
def memoryStaticArrayView (selector : Nat) (calldata : List Nat)
    (tupleHead memberWord elementWords freePointer : Nat) :
    Except DecodeFailure (ArrayView × Nat) := do
  let relative := loadWord selector calldata (word (tupleHead + 32*memberWord))
  if relative > 2^64-1 then throw .malformed
  let address := word (tupleHead + relative)
  if signedWord (word (address + 31)) ≥ signedWord (calldataSize calldata) then
    throw .malformed
  let length := loadWord selector calldata address
  if length > 2^64-1 then throw .allocation
  let next ← allocateWords freePointer (length + 1)
  let start := word (address + 32)
  let finish := word (start + word (32*elementWords*length))
  if finish > calldataSize calldata then throw .malformed
  pure (⟨start, length⟩, next)

/-- Supported unsigned scalar ABI shapes. Widths are intrinsically multiples
of eight in [8,256]; unsupported source types must be rejected while building
this schema, not converted to a malformed-input EVM result. -/
inductive ScalarKind where
  | uint (byteWidthMinusOne : Fin 32)
  | address
  | bool
  | bytes32
  deriving Repr, DecidableEq

def scalarBound : ScalarKind → Nat
  | .uint width => 2^(8*(width.val + 1))
  | .address => 2^160
  | .bool => 2
  | .bytes32 => modulus

def readScalar (selector : Nat) (calldata : List Nat) (offset : Nat)
    (kind : ScalarKind) : Except DecodeFailure Nat :=
  let value := loadWord selector calldata offset
  if value < scalarBound kind then .ok value else .error .malformed

/-- Read every member in declaration order. Used eagerly for memory tuples;
calldata member access instead calls `readScalar` only at the source read. -/
def readStaticFields (selector : Nat) (calldata : List Nat) :
    Nat → List ScalarKind → Except DecodeFailure (List Nat)
  | _, [] => .ok []
  | offset, kind :: rest => do
      let value ← readScalar selector calldata offset kind
      let values ← readStaticFields selector calldata (word (offset + 32)) rest
      pure (value :: values)

/-- Decode and allocate each static struct element after its array header.
The caller must first apply `memoryStaticArrayView`, retaining the complete
array bounds check before these element allocations and canonicality checks. -/
def readMemoryStaticElements (selector : Nat) (calldata : List Nat)
    (fields : List ScalarKind) : Nat → Nat → Nat →
      Except DecodeFailure (List (List Nat) × Nat)
  | _, freePointer, 0 => .ok ([], freePointer)
  | offset, freePointer, remaining + 1 => do
      if signedWord (subWord (calldataSize calldata) offset) < Int.ofNat (32*fields.length) then
        throw .malformed
      let next ← allocateWords freePointer fields.length
      let values ← readStaticFields selector calldata offset fields
      let (rest, finalPointer) ← readMemoryStaticElements selector calldata fields
        (word (offset + 32*fields.length)) next remaining
      pure (values :: rest, finalPointer)

end Compiler.CompilationModel.SolidityImport.SolidityAbi
