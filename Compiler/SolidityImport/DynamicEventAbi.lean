import Compiler.SolidityImport.SolidityAbi
import Compiler.SolidityImport.AbiLowering

namespace Compiler.CompilationModel.SolidityImport.DynamicEventAbi
open AbiLowering

/-!
The non-indexed payload of `emit E(...)` whose data arguments include dynamic
`T[] calldata` arrays of scalars, as executable model code matching solc's
`abi_encode_tuple_*_fromStack` for an event:

* the payload starts at `allocate_unbounded()` (`mload(0x40)`) and the free
  memory pointer is not advanced;
* static scalar arguments occupy one head word each, in source order;
* each array argument's head word is its tail offset from the payload start; its
  tail is the length word followed by one word per element;
* `uint256`/`bytes32`/`int256` elements are copied verbatim (solc's
  `copy_calldata_to_memory` / identity cleanup), and every narrower element is
  decoded with its validator, reverting with no data on a dirty word.

The caller supplies already-evaluated, cleaned scalar words, entry-decoded
calldata arrays (their offset/length checks ran at the root), and fresh names.
-/

/-- A non-indexed event argument, in source order. -/
inductive Argument where
  /-- A static scalar head word, already evaluated and cleaned. -/
  | word (value : Expr)
  /-- An entry-decoded `T[] calldata` array: element data offset and length. -/
  | calldataArray (data length : Expr) (kind : SolidityAbi.ScalarKind)

/-- Fresh names for one array's tail pointer, loop index and loaded element. -/
structure ArrayNames where
  tail : String
  index : String
  element : String
  deriving Inhabited

/-- Whether solc decodes each element with a validator. Full-word kinds have
identity cleanup, so their encoding is a verbatim copy. -/
def elementValidated (kind : SolidityAbi.ScalarKind) : Bool :=
  SolidityAbi.scalarBound kind < 2 ^ 256

/-- Number of array arguments, i.e. of `ArrayNames` the caller must supply. -/
def arrayCount : List Argument → Nat
  | [] => 0
  | .word _ :: rest => arrayCount rest
  | .calldataArray .. :: rest => arrayCount rest + 1

/-- The loop body storing element `index` of a calldata array at `tail`. -/
def elementBody (names : ArrayNames) (data : Expr) (kind : SolidityAbi.ScalarKind) :
    List Stmt :=
  let index := Expr.localVar names.index
  let source := Expr.calldataload (.add data (.mul index (.literal 32)))
  let target := Expr.add (.add (.localVar names.tail) (.literal 32)) (.mul index (.literal 32))
  if elementValidated kind then
    [ .letVar names.element source
    , guard (.lt (.localVar names.element) (.literal (SolidityAbi.scalarBound kind)))
    , .mstore target (.localVar names.element) ]
  else
    [.mstore target source]

/-- The head offset word and the tail of the array argument at head word
`headIndex`, whose tail starts at `position`. -/
def arrayTail (base : Expr) (headIndex : Nat) (position : Expr) (names : ArrayNames)
    (data length : Expr) (kind : SolidityAbi.ScalarKind) : List Stmt :=
  let tail := Expr.localVar names.tail
  [ .letVar names.tail position
  , .mstore (.add base (.literal (32 * headIndex))) (.sub tail base)
  , .mstore tail length
  , .forEach names.index length (elementBody names data kind) ]

/-- The first byte after an array tail. Lengths are entry-decoded (`< 2^64`), so
this sum cannot wrap. -/
def arrayEnd (names : ArrayNames) (length : Expr) : Expr :=
  .add (.localVar names.tail) (.add (.literal 32) (.mul length (.literal 32)))

/-- Head words and tails from head word `headIndex` on, with the next tail at
`position`; returns the statements and the payload end. -/
def encodeFrom (base : Expr) : Nat → Expr → List ArrayNames → List Argument →
    List Stmt × Expr
  | _, position, _, [] => ([], position)
  | headIndex, position, names, .word value :: rest =>
      let (body, finish) := encodeFrom base (headIndex + 1) position names rest
      (.mstore (.add base (.literal (32 * headIndex))) value :: body, finish)
  | headIndex, position, arrayNames :: names, .calldataArray data length kind :: rest =>
      let (body, finish) :=
        encodeFrom base (headIndex + 1) (arrayEnd arrayNames length) names rest
      (arrayTail base headIndex position arrayNames data length kind ++ body, finish)
  | _, position, [], .calldataArray .. :: _ => ([], position)

/-- The full payload: `pointer` is bound to `mload(0x40)` and `size` to the
encoded byte length. `names` must hold `arrayCount arguments` fresh entries;
`none` otherwise. -/
def encode (pointer size : String) (names : List ArrayNames) (arguments : List Argument) :
    Option (List Stmt) :=
  if names.length != arrayCount arguments then none else
  let base := Expr.localVar pointer
  let (body, finish) :=
    encodeFrom base 0 (.add base (.literal (32 * arguments.length))) names arguments
  some ([.letVar pointer (.mload (.literal 64))] ++ body ++ [.letVar size (.sub finish base)])

/-- Every name bound by `encode`, for the importer's reservation check. -/
def boundNames (pointer size : String) (names : List ArrayNames) : List String :=
  pointer :: size :: names.flatMap fun n => [n.tail, n.index, n.element]

/-- Static arguments do not allocate tails: an all-word payload is exactly its
head, written from the unbounded free-memory position. -/
theorem encodeFrom_words (base position : Expr) (headIndex : Nat) (names : List ArrayNames)
    (values : List Expr) :
    (encodeFrom base headIndex position names (values.map .word)).2 = position := by
  induction values generalizing headIndex with
  | nil => rfl
  | cons value rest ih => exact ih (headIndex + 1)

/-- Full-word elements are copied without a validator. -/
theorem elementValidated_uint256 : elementValidated (.uint ⟨31, by decide⟩) = false := by
  decide

/-- Addresses are decoded with solc's `validator_revert_t_address`. -/
theorem elementValidated_address : elementValidated .address = true := by
  decide

end Compiler.CompilationModel.SolidityImport.DynamicEventAbi
