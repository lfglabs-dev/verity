import Verity.Core.Model.Denote

/-!
# Denotation of the SHA-256 precompile

This module gives a compiler-free denotation of the call emitted by
`Compiler.Modules.Precompiles.sha256MemoryModule` without importing the compiler
layer.  The call reads an exact byte slice from EVM memory, performs a static
call to precompile address `0x02` with a 32-byte output area, writes the digest
word at the requested output offset, and propagates call failure as a revert.

The sole cryptographic assumption is the explicitly threaded
`sha256_correct` hypothesis below.  It says that a successful address-2 call
returns the FIPS 180-4 SHA-256 digest.  It deliberately does not assume that a
call succeeds: failure remains observable in the denotation.
-/

namespace Compiler.CompilationModel.Denote.Sha256

/-- The EVM address of the SHA-256 precompile. -/
def precompileAddress : Nat := 2

/-- The fixed output size of the SHA-256 precompile. -/
def digestSize : Nat := 32

/-- Read byte `index` from a word stored in EVM big-endian byte order. -/
def byteAt (word : Verity.Core.Uint256) (index : Nat) : UInt8 :=
  UInt8.ofNat (word.val / (2 ^ (8 * (31 - index % 32))) % 256)

/-- Read `size` bytes beginning at `offset` from the word-addressed memory
model.  Successive 32-byte chunks are based at `offset + 32*k`, matching the
memory regions produced by the compiler's contiguous `mstore` sequences. -/
def memorySlice (memory : Nat → Verity.Core.Uint256) (offset size : Nat) : ByteArray :=
  ⟨(List.range size).foldl (fun bytes index =>
      bytes.push (byteAt (memory (offset + 32 * (index / 32))) index)) #[]⟩

/-- A fully explicit EVM static-call request. -/
structure StaticCallRequest where
  address : Nat
  inputOffset : Nat
  inputSize : Nat
  outputOffset : Nat
  outputSize : Nat
  input : ByteArray

/-- The only call-level effects relevant to the SHA-256 precompile. -/
inductive StaticCallResult where
  | success (returnData : ByteArray)
  | failure

/-- External interpretation of a static call. -/
abbrev StaticCallOracle := StaticCallRequest → StaticCallResult

/-- Canonical request generated for an address-2 SHA-256 precompile call. -/
def request (memory : Nat → Verity.Core.Uint256)
    (inputOffset inputSize outputOffset : Nat) : StaticCallRequest where
  address := precompileAddress
  inputOffset := inputOffset
  inputSize := inputSize
  outputOffset := outputOffset
  outputSize := digestSize
  input := memorySlice memory inputOffset inputSize

/-- Convert the (big-endian) digest bytes returned by the precompile to the
word observed by `mload(outputOffset)`. -/
def digestWord (digest : ByteArray) : Verity.Core.Uint256 :=
  digest.foldl (fun acc byte => acc * 256 + byte.toNat) 0

/-- Write the single 32-byte digest word at the precompile output offset. -/
def writeDigest (world : Verity.ContractState) (outputOffset : Nat)
    (digest : ByteArray) : Verity.ContractState :=
  { world with memory := fun offset =>
      if offset = outputOffset then digestWord digest else world.memory offset }

/-- Result of the SHA-256 call fragment.  A failed static call becomes a
revert; a successful call exposes the digest word and updated memory. -/
inductive Outcome where
  | success (digest : Verity.Core.Uint256) (world : Verity.ContractState)
  | revert

/-- Denote the compiler-emitted
`staticcall(gas(), 2, inputOffset, inputSize, outputOffset, 32)` fragment.
Failure is propagated and successful return data must be exactly one digest. -/
def denote (oracle : StaticCallOracle) (world : Verity.ContractState)
    (inputOffset inputSize outputOffset : Nat) : Outcome :=
  match oracle (request world.memory inputOffset inputSize outputOffset) with
  | .failure => .revert
  | .success digest =>
      if digest.size = digestSize then
        .success (digestWord digest) (writeDigest world outputOffset digest)
      else
        .revert

/-- The named FIPS assumption.  `fipsSha256` denotes SHA-256 as specified by
FIPS 180-4; the hypothesis states that every successful EVM precompile call at
address `0x02` returns exactly that 32-byte digest for the requested memory
slice.  It makes no availability/success assumption. -/
def sha256_correct (oracle : StaticCallOracle)
    (fipsSha256 : ByteArray → ByteArray) : Prop :=
  ∀ req digest,
    req.address = precompileAddress →
    req.outputSize = digestSize →
    oracle req = .success digest →
    digest = fipsSha256 req.input ∧ digest.size = digestSize

/-! ## Slice, offset, and padding facts -/

@[simp] theorem memorySlice_size (memory : Nat → Verity.Core.Uint256) (offset size : Nat) :
    (memorySlice memory offset size).size = size := by
  simp [memorySlice, ByteArray.size]

@[simp] theorem request_address (memory : Nat → Verity.Core.Uint256)
    (inputOffset inputSize outputOffset : Nat) :
    (request memory inputOffset inputSize outputOffset).address = precompileAddress := rfl

@[simp] theorem request_inputOffset (memory : Nat → Verity.Core.Uint256)
    (inputOffset inputSize outputOffset : Nat) :
    (request memory inputOffset inputSize outputOffset).inputOffset = inputOffset := rfl

@[simp] theorem request_inputSize (memory : Nat → Verity.Core.Uint256)
    (inputOffset inputSize outputOffset : Nat) :
    (request memory inputOffset inputSize outputOffset).inputSize = inputSize := rfl

@[simp] theorem request_outputOffset (memory : Nat → Verity.Core.Uint256)
    (inputOffset inputSize outputOffset : Nat) :
    (request memory inputOffset inputSize outputOffset).outputOffset = outputOffset := rfl

@[simp] theorem request_outputSize (memory : Nat → Verity.Core.Uint256)
    (inputOffset inputSize outputOffset : Nat) :
    (request memory inputOffset inputSize outputOffset).outputSize = digestSize := rfl

@[simp] theorem request_input_size (memory : Nat → Verity.Core.Uint256)
    (inputOffset inputSize outputOffset : Nat) :
    (request memory inputOffset inputSize outputOffset).input.size = inputSize := by
  simp [request]

/-- The precompile hashes the exact requested length: no ABI or word padding is
included in the request, even when the final memory word is only partial. -/
theorem request_has_no_input_padding (memory : Nat → Verity.Core.Uint256)
    (inputOffset inputSize outputOffset padding : Nat) (hpadding : 0 < padding) :
    (request memory inputOffset inputSize outputOffset).input.size < inputSize + padding := by
  simp only [request_input_size]
  omega

@[simp] theorem writeDigest_at (world : Verity.ContractState) (outputOffset : Nat)
    (digest : ByteArray) :
    (writeDigest world outputOffset digest).memory outputOffset = digestWord digest := by
  simp [writeDigest]

theorem writeDigest_away (world : Verity.ContractState) (outputOffset offset : Nat)
    (digest : ByteArray) (hne : offset ≠ outputOffset) :
    (writeDigest world outputOffset digest).memory offset = world.memory offset := by
  simp [writeDigest, hne]

/-! ## Failure and composition -/

theorem denote_failure (oracle : StaticCallOracle) (world : Verity.ContractState)
    (inputOffset inputSize outputOffset : Nat)
    (hfail : oracle (request world.memory inputOffset inputSize outputOffset) = .failure) :
    denote oracle world inputOffset inputSize outputOffset = .revert := by
  simp [denote, hfail]

/-- Composition theorem connecting slicing, the address-2 static call, FIPS
correctness, the 32-byte output check, and the final memory write. -/
theorem denote_success_compose (oracle : StaticCallOracle)
    (fipsSha256 : ByteArray → ByteArray) (world : Verity.ContractState)
    (inputOffset inputSize outputOffset : Nat) (digest : ByteArray)
    (sha256_correct : sha256_correct oracle fipsSha256)
    (hcall : oracle (request world.memory inputOffset inputSize outputOffset) =
      .success digest) :
    denote oracle world inputOffset inputSize outputOffset =
      .success
        (digestWord (fipsSha256 (memorySlice world.memory inputOffset inputSize)))
        (writeDigest world outputOffset
          (fipsSha256 (memorySlice world.memory inputOffset inputSize))) := by
  have hcorrect := sha256_correct
    (request world.memory inputOffset inputSize outputOffset)
    digest rfl rfl hcall
  have heq : digest = fipsSha256 (memorySlice world.memory inputOffset inputSize) := by
    simpa [request] using hcorrect.1
  have hsize : (fipsSha256 (memorySlice world.memory inputOffset inputSize)).size =
      digestSize := by
    rw [← heq]
    exact hcorrect.2
  rw [heq] at hcall
  simp [denote, hcall, hsize, digestSize]

end Compiler.CompilationModel.Denote.Sha256
