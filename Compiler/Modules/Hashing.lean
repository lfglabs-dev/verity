/-
  Compiler.Modules.Hashing: static ABI and packed hash helpers

  These helpers cover common audit-modeling hash preimages:
  - static ABI-encoded 32-byte words
  - static 32-byte words
  - static byte-width segments from 1 to 32 bytes
  - the final EIP-712 typed-data digest preimage

  They intentionally do not model dynamic Solidity packed encoding for bytes or
  strings yet.
-/

import Compiler.ECM
import Compiler.CompilationModel

namespace Compiler.Modules.Hashing

open Compiler.Yul
open Compiler.ECM
open Compiler.CompilationModel (Stmt Expr freeMemoryPointer)

private def packedWordTempName (idx : Nat) : String :=
  s!"__packed_word_{idx}"

private def packedWordBindings (words : List YulExpr) : List YulStmt :=
  words.zipIdx.map fun (word, idx) =>
    YulStmt.let_ (packedWordTempName idx) word

private def packedWordTempStoresAt (base : YulExpr) (wordCount : Nat) : List YulStmt :=
  (List.range wordCount).map fun idx =>
    YulStmt.exprStmt (YulExpr.call "mstore" [
      YulExpr.call "add" [base, YulExpr.lit (idx * 32)],
      YulExpr.ident (packedWordTempName idx)
    ])

private def alignUp32 (n : Nat) : Nat :=
  ((n + 31) / 32) * 32

private def packedSegmentMask (width : Nat) : Nat :=
  2 ^ (width * 8) - 1

private def packedSegmentTempStoreAt (base : YulExpr) (offset width idx : Nat) : YulStmt :=
  let value := YulExpr.ident (packedWordTempName idx)
  let stored :=
    if width == 32 then
      value
    else
      YulExpr.call "shl" [
        YulExpr.lit ((32 - width) * 8),
        YulExpr.call "and" [value, YulExpr.hex (packedSegmentMask width)]
      ]
  YulStmt.exprStmt (YulExpr.call "mstore" [
    YulExpr.call "add" [base, YulExpr.lit offset],
    stored
  ])

private def packedSegmentTempStoresAtAux (base : YulExpr) (offset : Nat) : List Nat → Nat → List YulStmt
  | [], _ => []
  | width :: widths, idx =>
      packedSegmentTempStoreAt base offset width idx ::
        packedSegmentTempStoresAtAux base (offset + width) widths (idx + 1)

private def packedSegmentTempStoresAt (base : YulExpr) (widths : List Nat) : List YulStmt :=
  packedSegmentTempStoresAtAux base 0 widths 0

private def validatePackedSegmentWidths (moduleName : String) (widths : List Nat) : Except String Unit :=
  widths.forM fun width =>
    if width == 0 || width > 32 then
      throw s!"{moduleName} segment widths must be between 1 and 32 bytes"
    else
      pure ()

/-- Keccak-256 over packed static 32-byte words stored at free memory.
    This is the static-word subset of Solidity `abi.encodePacked(...)` followed
    by `keccak256`. -/
def abiEncodePackedWordsModule (resultVar : String) (wordCount : Nat) : ExternalCallModule where
  name := "abiEncodePackedWords"
  numArgs := wordCount
  resultVars := [resultVar]
  writesState := false
  readsState := false
  axioms := ["keccak256_memory_slice_matches_evm", "abi_packed_static_word_layout"]
  compile := fun _ctx args => do
    if args.length != wordCount then
      throw s!"abiEncodePackedWords expects {wordCount} static word argument(s)"
    let size := wordCount * 32
    let ptrName := s!"__{resultVar}_packed_words_ptr"
    let ptr := YulExpr.ident ptrName
    pure [
      YulStmt.let_ resultVar (YulExpr.lit 0),
      YulStmt.block (
        packedWordBindings args ++
        [YulStmt.let_ ptrName (YulExpr.call "mload" [YulExpr.lit freeMemoryPointer])] ++
        packedWordTempStoresAt ptr wordCount ++
        [
      YulStmt.exprStmt (YulExpr.call "mstore" [
        YulExpr.lit freeMemoryPointer,
        YulExpr.call "add" [ptr, YulExpr.lit (alignUp32 size)]
      ]),
      YulStmt.assign resultVar (YulExpr.call "keccak256" [ptr, YulExpr.lit size])
      ])
    ]

/-- Convenience constructor for static-word packed Keccak hashing. -/
def abiEncodePackedWords (resultVar : String) (words : List Expr) : Stmt :=
  .ecm (abiEncodePackedWordsModule resultVar words.length) words

/-- Short alias for the static 32-byte-word subset of `abi.encodePacked`.
    Use `abiEncodePackedWords` when the narrower semantics should be explicit at
    the call site. -/
def abiEncodePacked (resultVar : String) (words : List Expr) : Stmt :=
  abiEncodePackedWords resultVar words

/-- Keccak-256 over Solidity `abi.encode(...)` for static values already
    represented as full ABI words.

    For complete-word static values, the ABI encoding is the contiguous sequence
    of 32-byte words. Sub-word normalization (for example address/bool masking)
    is expected to happen at the expression/lowering layer before this helper is
    called. -/
def abiEncodeStaticWordsModule (resultVar : String) (wordCount : Nat) : ExternalCallModule where
  name := "abiEncodeStaticWords"
  numArgs := wordCount
  resultVars := [resultVar]
  writesState := false
  readsState := false
  axioms := ["keccak256_memory_slice_matches_evm", "abi_standard_static_word_layout"]
  compile := fun _ctx args => do
    if args.length != wordCount then
      throw s!"abiEncodeStaticWords expects {wordCount} static word argument(s)"
    let size := wordCount * 32
    let ptrName := s!"__{resultVar}_abi_static_words_ptr"
    let ptr := YulExpr.ident ptrName
    pure [
      YulStmt.let_ resultVar (YulExpr.lit 0),
      YulStmt.block (
        packedWordBindings args ++
        [YulStmt.let_ ptrName (YulExpr.call "mload" [YulExpr.lit freeMemoryPointer])] ++
        packedWordTempStoresAt ptr wordCount ++
        [
          YulStmt.exprStmt (YulExpr.call "mstore" [
            YulExpr.lit freeMemoryPointer,
            YulExpr.call "add" [ptr, YulExpr.lit (alignUp32 size)]
          ]),
          YulStmt.assign resultVar (YulExpr.call "keccak256" [ptr, YulExpr.lit size])
        ])
    ]

/-- Convenience constructor for `keccak256(abi.encode(...))` over static ABI
    word arguments. -/
def abiEncodeStaticWords (resultVar : String) (words : List Expr) : Stmt :=
  .ecm (abiEncodeStaticWordsModule resultVar words.length) words

/-- EIP-712 `hashStruct(s) = keccak256(abi.encode(typeHash, ...members))`
    for static word members. This is deliberately a thin wrapper around the
    audited static ABI-word helper, so it introduces no new ECM or trust
    boundary. -/
def eip712HashStruct (resultVar : String) (typeHash : Expr) (members : List Expr) : Stmt :=
  abiEncodeStaticWords resultVar (typeHash :: members)

private def yulAdd (base : YulExpr) (offset : Nat) : YulExpr :=
  YulExpr.call "add" [base, YulExpr.lit offset]

/-- Concrete six-word Permit struct-hash Yul layout:
    `keccak256(abi.encode(typeHash, owner, spender, value, nonce, deadline))`. -/
def permitStructHashExpectedYul (typeHash : Nat) : List YulStmt :=
  let resultVar := "structHash"
  let ptrName := s!"__{resultVar}_abi_static_words_ptr"
  let ptr := YulExpr.ident ptrName
  let args :=
    [ YulExpr.lit typeHash
    , YulExpr.ident "owner"
    , YulExpr.ident "spender"
    , YulExpr.ident "value"
    , YulExpr.ident "nonce"
    , YulExpr.ident "deadline"
    ]
  [ YulStmt.let_ resultVar (YulExpr.lit 0)
  , YulStmt.block (
      packedWordBindings args ++
      [YulStmt.let_ ptrName (YulExpr.call "mload" [YulExpr.lit freeMemoryPointer])] ++
      packedWordTempStoresAt ptr 6 ++
      [ YulStmt.exprStmt (YulExpr.call "mstore"
          [ YulExpr.lit freeMemoryPointer
          , yulAdd ptr 192
          ])
      , YulStmt.assign resultVar
          (YulExpr.call "keccak256"
            [ptr, YulExpr.lit 192])
      ])
  ]

theorem abiEncodeStaticWordsModule_compile_permitStructHash_layout (typeHash : Nat) :
    (abiEncodeStaticWordsModule "structHash" 6).compile {}
      [ YulExpr.lit typeHash
      , YulExpr.ident "owner"
      , YulExpr.ident "spender"
      , YulExpr.ident "value"
      , YulExpr.ident "nonce"
      , YulExpr.ident "deadline"
      ] =
    Except.ok (permitStructHashExpectedYul typeHash) := by
  simp [abiEncodeStaticWordsModule, permitStructHashExpectedYul,
    packedWordBindings, packedWordTempStoresAt, packedWordTempName,
    alignUp32, yulAdd, Bind.bind, Except.bind, Pure.pure, Except.pure]

/-- Keccak-256 over Solidity `abi.encode(array)` for a direct dynamic-array
    parameter whose elements have a fixed static word width.

    The module takes the array length as its single expression argument and
    references `{arrayParam}_data_offset` emitted by the calldata/internal
    dynamic-array lowering. It encodes the single dynamic-array argument as:

      head offset (32), array length, contiguous static element words

    This covers arrays such as `uint256[]`, `address[]`, and arrays of static
    tuples/structs when the caller supplies the element word width. -/
def abiEncodeStaticArrayModule
    (resultVar arrayParam : String) (elementWords : Nat) : ExternalCallModule where
  name := "abiEncodeStaticArray"
  numArgs := 1
  resultVars := [resultVar]
  writesState := false
  readsState := false
  axioms := ["keccak256_memory_slice_matches_evm", "abi_standard_dynamic_array_static_element_layout"]
  compile := fun ctx args => do
    let arrayLengthExpr ←
      match args with
      | [arrayLengthExpr] => pure arrayLengthExpr
      | _ => throw s!"abiEncodeStaticArray expects 1 expression argument, got {args.length}"
    if arrayParam.isEmpty then
      throw "abiEncodeStaticArray requires a non-empty array parameter name"
    if elementWords == 0 then
      throw "abiEncodeStaticArray requires elementWords > 0"
    let ptrName := s!"__{resultVar}_abi_array_ptr"
    let lengthName := s!"__{resultVar}_abi_array_length"
    let dataBytesName := s!"__{resultVar}_abi_array_data_bytes"
    let totalBytesName := s!"__{resultVar}_abi_array_total_bytes"
    let paddedTotalName := s!"__{resultVar}_abi_array_padded_total"
    let ptr := YulExpr.ident ptrName
    let length := YulExpr.ident lengthName
    let dataBytes := YulExpr.ident dataBytesName
    let totalBytes := YulExpr.ident totalBytesName
    pure [
      YulStmt.block ([
        YulStmt.let_ ptrName (YulExpr.call "mload" [YulExpr.lit freeMemoryPointer]),
        YulStmt.let_ lengthName arrayLengthExpr,
        YulStmt.exprStmt (YulExpr.call "mstore" [ptr, YulExpr.lit 32]),
        YulStmt.exprStmt (YulExpr.call "mstore" [
          YulExpr.call "add" [ptr, YulExpr.lit 32],
          length
        ]),
        YulStmt.let_ dataBytesName (YulExpr.call "mul" [
          length,
          YulExpr.lit (elementWords * 32)
        ])
      ] ++ ECM.dynamicCopyData ctx
        (YulExpr.call "add" [ptr, YulExpr.lit 64])
        (YulExpr.ident s!"{arrayParam}_data_offset")
        dataBytes ++ [
        YulStmt.let_ totalBytesName (YulExpr.call "add" [YulExpr.lit 64, dataBytes]),
        YulStmt.let_ paddedTotalName (YulExpr.call "and" [
          YulExpr.call "add" [totalBytes, YulExpr.lit 31],
          YulExpr.call "not" [YulExpr.lit 31]
        ]),
        YulStmt.exprStmt (YulExpr.call "mstore" [
          YulExpr.lit freeMemoryPointer,
          YulExpr.call "add" [ptr, YulExpr.ident paddedTotalName]
        ]),
        YulStmt.let_ resultVar (YulExpr.call "keccak256" [ptr, totalBytes])
      ])
    ]

/-- Convenience constructor for `keccak256(abi.encode(array))` over static-width
    dynamic-array parameters. -/
def abiEncodeStaticArray
    (resultVar arrayParam : String) (elementWords : Nat) (arrayLength : Expr) : Stmt :=
  .ecm (abiEncodeStaticArrayModule resultVar arrayParam elementWords) [arrayLength]

/-- Keccak-256 over packed static byte-width segments stored at free memory.
    Each argument is encoded as exactly the matching byte width from `widths`,
    using Solidity's left-aligned memory representation for sub-word static
    values. Sub-word values are masked to their requested width before being
    shifted into position. Widths must be between 1 and 32 bytes. -/
def abiEncodePackedStaticSegmentsModule (resultVar : String) (widths : List Nat) : ExternalCallModule where
  name := "abiEncodePackedStaticSegments"
  numArgs := widths.length
  resultVars := [resultVar]
  writesState := false
  readsState := false
  axioms := ["keccak256_memory_slice_matches_evm", "abi_packed_static_segment_layout"]
  compile := fun _ctx args => do
    if args.length != widths.length then
      throw s!"abiEncodePackedStaticSegments expects {widths.length} static segment argument(s)"
    validatePackedSegmentWidths "abiEncodePackedStaticSegments" widths
    let size := widths.foldl (· + ·) 0
    let ptrName := s!"__{resultVar}_packed_segments_ptr"
    let ptr := YulExpr.ident ptrName
    pure [
      YulStmt.let_ resultVar (YulExpr.lit 0),
      YulStmt.block (
        packedWordBindings args ++
        [YulStmt.let_ ptrName (YulExpr.call "mload" [YulExpr.lit freeMemoryPointer])] ++
        packedSegmentTempStoresAt ptr widths ++
        [
          YulStmt.exprStmt (YulExpr.call "mstore" [
            YulExpr.lit freeMemoryPointer,
            YulExpr.call "add" [ptr, YulExpr.lit (alignUp32 size)]
          ]),
          YulStmt.assign resultVar (YulExpr.call "keccak256" [ptr, YulExpr.lit size])
        ])
    ]

/-- Convenience constructor for static byte-width packed Keccak hashing. -/
def abiEncodePackedStaticSegments (resultVar : String) (segments : List (Expr × Nat)) : Stmt :=
  .ecm (abiEncodePackedStaticSegmentsModule resultVar (segments.map Prod.snd))
    (segments.map Prod.fst)

/-- EIP-712 typed-data digest helper.

    Computes `keccak256(abi.encodePacked(hex"1901", domainSeparator, structHash))`
    over a scratch memory slice. The cryptographic Keccak equivalence remains
    the standard memory-slice Keccak assumption, while the helper fixes the
    byte-exact EIP-712 preimage layout at one audited call site. -/
def eip712DigestModule (resultVar : String) : ExternalCallModule where
  name := "eip712Digest"
  numArgs := 2
  resultVars := [resultVar]
  writesState := false
  readsState := false
  axioms := ["keccak256_memory_slice_matches_evm", "eip712_digest_layout"]
  compile := fun _ctx args => do
    let (domainSeparatorExpr, structHashExpr) ←
      match args with
      | [domainSeparatorExpr, structHashExpr] => pure (domainSeparatorExpr, structHashExpr)
      | _ => throw s!"eip712Digest expects 2 arguments (domainSeparator, structHash)"
    let ptrName := s!"__{resultVar}_eip712_ptr"
    let ptr := YulExpr.ident ptrName
    pure [
      YulStmt.let_ resultVar (YulExpr.lit 0),
      YulStmt.block [
        YulStmt.let_ ptrName (YulExpr.call "mload" [YulExpr.lit freeMemoryPointer]),
        YulStmt.exprStmt (YulExpr.call "mstore" [
          ptr,
          YulExpr.call "shl" [YulExpr.lit 240, YulExpr.hex 0x1901]
        ]),
        YulStmt.exprStmt (YulExpr.call "mstore" [
          YulExpr.call "add" [ptr, YulExpr.lit 2],
          domainSeparatorExpr
        ]),
        YulStmt.exprStmt (YulExpr.call "mstore" [
          YulExpr.call "add" [ptr, YulExpr.lit 34],
          structHashExpr
        ]),
        YulStmt.exprStmt (YulExpr.call "mstore" [
          YulExpr.lit freeMemoryPointer,
          YulExpr.call "add" [ptr, YulExpr.lit 96]
        ]),
        YulStmt.assign resultVar (YulExpr.call "keccak256" [ptr, YulExpr.lit 66])
      ]
    ]

/-- Convenience constructor for EIP-712 typed-data digest hashing. -/
def eip712Digest (resultVar : String) (domainSeparator structHash : Expr) : Stmt :=
  .ecm (eip712DigestModule resultVar) [domainSeparator, structHash]

/-- Concrete EIP-712 digest Yul layout:
    `keccak256(0x1901 ++ domainSeparator ++ structHash)`. -/
def eip712DigestExpectedYul : List YulStmt :=
  let resultVar := "digest"
  let ptrName := s!"__{resultVar}_eip712_ptr"
  let ptr := YulExpr.ident ptrName
  [ YulStmt.let_ resultVar (YulExpr.lit 0)
  , YulStmt.block
      [ YulStmt.let_ ptrName
          (YulExpr.call "mload" [YulExpr.lit freeMemoryPointer])
      , YulStmt.exprStmt (YulExpr.call "mstore"
          [ ptr
          , YulExpr.call "shl" [YulExpr.lit 240, YulExpr.hex 0x1901]
          ])
      , YulStmt.exprStmt (YulExpr.call "mstore"
          [yulAdd ptr 2, YulExpr.ident "domainSeparator"])
      , YulStmt.exprStmt (YulExpr.call "mstore"
          [yulAdd ptr 34, YulExpr.ident "structHash"])
      , YulStmt.exprStmt (YulExpr.call "mstore"
          [ YulExpr.lit freeMemoryPointer
          , yulAdd ptr 96
          ])
      , YulStmt.assign resultVar
          (YulExpr.call "keccak256"
            [ptr, YulExpr.lit 66])
      ]
  ]

theorem eip712DigestModule_compile_digest_layout :
    (eip712DigestModule "digest").compile {}
      [YulExpr.ident "domainSeparator", YulExpr.ident "structHash"] =
    Except.ok eip712DigestExpectedYul := by
  simp [eip712DigestModule, eip712DigestExpectedYul, yulAdd,
    Bind.bind, Except.bind, Pure.pure, Except.pure]

/-- SHA-256 over packed static 32-byte words stored at free memory.
    The digest is written after the packed input words and then bound from
    memory, avoiding overlap with the preimage. -/
def sha256PackedWordsModule (resultVar : String) (wordCount : Nat) : ExternalCallModule where
  name := "sha256PackedWords"
  numArgs := wordCount
  resultVars := [resultVar]
  writesState := false
  readsState := true
  axioms := ["evm_sha256_precompile", "abi_packed_static_word_layout"]
  compile := fun _ctx args => do
    if args.length != wordCount then
      throw s!"sha256PackedWords expects {wordCount} static word argument(s)"
    let size := wordCount * 32
    let ptrName := s!"__{resultVar}_sha256_packed_words_ptr"
    let outputOffsetName := s!"__{resultVar}_sha256_packed_words_output"
    let ptr := YulExpr.ident ptrName
    let outputOffset := YulExpr.ident outputOffsetName
    let callExpr := YulExpr.call "staticcall" [
      YulExpr.call "gas" [],
      YulExpr.lit 2,
      ptr, YulExpr.lit size,
      outputOffset, YulExpr.lit 32
    ]
    let revertBlock := YulStmt.if_ (YulExpr.call "iszero" [YulExpr.ident "__sha256_packed_success"]) [
      YulStmt.exprStmt (YulExpr.call "revert" [YulExpr.lit 0, YulExpr.lit 0])
    ]
    pure [
      YulStmt.let_ resultVar (YulExpr.lit 0),
      YulStmt.block (packedWordBindings args ++ [
        YulStmt.let_ ptrName (YulExpr.call "mload" [YulExpr.lit freeMemoryPointer]),
        YulStmt.let_ outputOffsetName (YulExpr.call "add" [ptr, YulExpr.lit (alignUp32 size)])
      ] ++ packedWordTempStoresAt ptr wordCount ++ [
        YulStmt.let_ "__sha256_packed_success" callExpr,
        revertBlock,
        YulStmt.assign resultVar (YulExpr.call "mload" [outputOffset]),
        YulStmt.exprStmt (YulExpr.call "mstore" [
          YulExpr.lit freeMemoryPointer,
          YulExpr.call "add" [outputOffset, YulExpr.lit 32]
        ])
      ])
    ]

/-- Convenience constructor for static-word packed SHA-256 hashing. -/
def sha256PackedWords (resultVar : String) (words : List Expr) : Stmt :=
  .ecm (sha256PackedWordsModule resultVar words.length) words

/-- Short alias for static 32-byte-word packed SHA-256 preimages. -/
def sha256Packed (resultVar : String) (words : List Expr) : Stmt :=
  sha256PackedWords resultVar words

/-- SHA-256 over packed static byte-width segments.
    The digest is written at the next 32-byte-aligned offset after the preimage
    to avoid overlapping with non-word-sized packed input bytes. Sub-word
    values are masked to their requested width before being shifted into
    position. -/
def sha256PackedStaticSegmentsModule (resultVar : String) (widths : List Nat) : ExternalCallModule where
  name := "sha256PackedStaticSegments"
  numArgs := widths.length
  resultVars := [resultVar]
  writesState := false
  readsState := true
  axioms := ["evm_sha256_precompile", "abi_packed_static_segment_layout"]
  compile := fun _ctx args => do
    if args.length != widths.length then
      throw s!"sha256PackedStaticSegments expects {widths.length} static segment argument(s)"
    validatePackedSegmentWidths "sha256PackedStaticSegments" widths
    let size := widths.foldl (· + ·) 0
    let ptrName := s!"__{resultVar}_sha256_packed_segments_ptr"
    let outputOffsetName := s!"__{resultVar}_sha256_packed_segments_output"
    let ptr := YulExpr.ident ptrName
    let outputOffset := YulExpr.ident outputOffsetName
    let callExpr := YulExpr.call "staticcall" [
      YulExpr.call "gas" [],
      YulExpr.lit 2,
      ptr, YulExpr.lit size,
      outputOffset, YulExpr.lit 32
    ]
    let revertBlock := YulStmt.if_ (YulExpr.call "iszero" [YulExpr.ident "__sha256_packed_segments_success"]) [
      YulStmt.exprStmt (YulExpr.call "revert" [YulExpr.lit 0, YulExpr.lit 0])
    ]
    pure [
      YulStmt.let_ resultVar (YulExpr.lit 0),
      YulStmt.block (packedWordBindings args ++ [
        YulStmt.let_ ptrName (YulExpr.call "mload" [YulExpr.lit freeMemoryPointer]),
        YulStmt.let_ outputOffsetName (YulExpr.call "add" [ptr, YulExpr.lit (alignUp32 size)])
      ] ++ packedSegmentTempStoresAt ptr widths ++ [
        YulStmt.let_ "__sha256_packed_segments_success" callExpr,
        revertBlock,
        YulStmt.assign resultVar (YulExpr.call "mload" [outputOffset]),
        YulStmt.exprStmt (YulExpr.call "mstore" [
          YulExpr.lit freeMemoryPointer,
          YulExpr.call "add" [outputOffset, YulExpr.lit 32]
        ])
      ])
    ]

/-- Convenience constructor for static byte-width packed SHA-256 hashing. -/
def sha256PackedStaticSegments (resultVar : String) (segments : List (Expr × Nat)) : Stmt :=
  .ecm (sha256PackedStaticSegmentsModule resultVar (segments.map Prod.snd))
    (segments.map Prod.fst)

end Compiler.Modules.Hashing
