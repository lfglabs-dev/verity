import Compiler.CompilationModel

namespace Compiler.CompilationModel.SolidityImport.AbiEncoding

/-- Store canonical static ABI words in a fresh allocation. Every store and
the eventual hash use the same word grid. This avoids assuming byte-addressed
overlapping stores in Denote's word-memory representation.

`base` must already be bound, and the allocation must not overlap live memory.
The importer must validate the scalar schema and evaluate arguments before
calling this helper; this function does not admit any Solidity construct. -/
def wordStores (base : Expr) (words : List Expr) : List Stmt :=
  words.zipIdx.map fun (value, index) =>
    .mstore (.add base (.literal (32 * index))) value

/-- Allocate a static encoding using the Solidity free-memory pointer. The
fresh `baseName` and `endName` bindings must not alias each other or source
bindings. Overflow and excessive allocation produce Panic(0x41), matching
the memory-allocation guard already used by ABI decoding.

The caller initializes memory[64] at entry. All supported allocations have
word-multiple size, so aligned entry memory remains aligned. The returned
buffer contains no length word: it is the payload of `abi.encode`. -/
def staticWords (baseName endName : String) (words : List Expr) : List Stmt :=
  let base := Expr.localVar baseName
  let finish := Expr.localVar endName
  [ .letVar baseName (.mload (.literal 64))
  , .letVar endName (.add base (.literal (32 * words.length)))
  , .ite (.le finish (.literal (2^64-1))) [] [.panicCode (.literal 0x41)]
  , .ite (.ge finish base) [] [.panicCode (.literal 0x41)]
  , .mstore (.literal 64) finish ] ++ wordStores base words

/-- Reserve a runtime-sized word-aligned encoding tail. The schema/decoder
must establish a bounded size and alignment before using this primitive. -/
def reserve (baseName endName : String) (size : Expr) : List Stmt :=
  let base := Expr.localVar baseName
  let finish := Expr.localVar endName
  [ .letVar baseName (.mload (.literal 64))
  , .letVar endName (.add base size)
  , .ite (.le finish (.literal (2^64-1))) [] [.panicCode (.literal 0x41)]
  , .ite (.ge finish base) [] [.panicCode (.literal 0x41)]
  , .mstore (.literal 64) finish ]

/-- Byte position within a word, expressed using already covered unsigned
arithmetic. The quotient is exact before subtraction, so it cannot underflow. -/
def byteLane (index : Expr) : Expr :=
  .sub index (.mul (.div index (.literal 32)) (.literal 32))

def byteWordOffset (index : Expr) : Expr :=
  .mul (.div index (.literal 32)) (.literal 32)

/-- Copy bytes using only aligned word loads/stores. The destination was
zero-filled and this slice must be disjoint from previous copied slices;
addition then inserts a byte into a zero lane, without a carry. Source and
output allocations must be disjoint. No unaligned mstore/mload is assumed.

AbiMemory proves the actual emitted loop for local buffer/start bindings under
explicit freshness, bounds, alignment, nonoverlap and zero-destination premises. -/
def copyBytes (source destination start size : Expr)
    (indexName byteName addressName : String) : Stmt :=
  let index := Expr.localVar indexName
  let outputIndex := Expr.add start index
  let shift := fun position => Expr.mul (.literal 8) (.sub (.literal 31) (byteLane position))
  let sourceWord := Expr.mload (.add source (byteWordOffset index))
  let address := Expr.localVar addressName
  .forEach indexName size [
    .letVar byteName (.bitAnd (.shr (shift index) sourceWord) (.literal 255)),
    .letVar addressName (.add destination (byteWordOffset outputIndex)),
    .mstore address (.add (.mload address) (.shl (shift outputIndex) (.localVar byteName)))]

/-- Allocate and clear the final packed buffer. Length is bytes, allocation
is rounded up to whole words. Names are fresh; size is schema-bounded so the
rounding addition cannot wrap. The buffer carries no ABI length prefix. -/
def packedBuffer (baseName endName indexName : String) (size : Expr) : List Stmt :=
  let count := Expr.div (.add size (.literal 31)) (.literal 32)
  reserve baseName endName (.mul count (.literal 32)) ++
    [.forEach indexName count [.mstore
      (.add (.localVar baseName) (.mul (.localVar indexName) (.literal 32))) (.literal 0)]]

/-- Word-grid locations stay aligned. This is one necessary representation
condition, not a proof of the byte-copy loop's semantics. -/
theorem byte_word_address_aligned (base index : Nat) (aligned : base % 32 = 0) :
    (base + index / 32 * 32) % 32 = 0 := by
  omega

/-- A static ABI payload occupies one full word per scalar. This elementary
fact is separate from any claim of equivalence to solc or hash correctness. -/
theorem wordStores_length (base : Expr) (words : List Expr) :
    (wordStores base words).length = words.length := by
  simp [wordStores]

theorem staticWords_length (baseName endName : String) (words : List Expr) :
    (staticWords baseName endName words).length = 5 + words.length := by
  simp [staticWords, wordStores]
  omega

end Compiler.CompilationModel.SolidityImport.AbiEncoding
