import Compiler.Modules.Hashing
import Compiler.Keccak.MemorySlice
import Compiler.Proofs.IRGeneration.IRInterpreter
import Verity.Core.Model.ByteMemoryInverse

/-!
# EIP-712 digest preimage layout

`Compiler.Modules.Hashing.eip712DigestModule` hashes a 66-byte scratch slice built by three
overlapping `mstore`s at the free pointer `p`:

* `mstore(p, shl(240, 0x1901))`,
* `mstore(add(p, 2), domainSeparator)`,
* `mstore(add(p, 34), structHash)`,

then bumps the free pointer (`mstore(0x40, add(p, 96))`) and binds
`keccak256(p, 66)`. This module proves that the hashed bytes are exactly
`0x19 ‖ 0x01 ‖ BE32 domainSeparator ‖ BE32 structHash`:

* `slice_eip712LayoutMemory`: the byte-level layout of the three writes;
* `irMemorySliceBytesBE_eip712`: the IR word view of that memory serializes, for the
  `keccak256(p, 66)` read, to `eip712Preimage ds sh`;
* `abstractKeccakMemorySlice_eip712`: the IR `keccak256(p, 66)` of that memory is
  `eip712DigestValue ds sh`, the Keccak-256 of `eip712Preimage ds sh`;
* `eip712Digest_preimage_layout`: executing the emitted Yul (`eip712DigestExpectedYul`,
  which `eip712DigestModule_compile_digest_layout` pins as the module's output) from a
  state whose free pointer is `p` (with `96 ≤ p` and `p + 96 < 2^256`) continues, leaves
  `eip712Preimage ds sh` as the 66 bytes `keccak256(p, 66)` reads, and binds `digest` to
  `eip712DigestValue ds sh`.

`96 ≤ p` is needed: the free-pointer bump at `0x40` would otherwise overwrite the preimage.

Only the Keccak/EVM equivalence (`keccak256_memory_slice_matches_evm`) stays assumed.
-/

namespace Compiler.Proofs.Eip712DigestLayout

open Compiler.CompilationModel.DenoteMemory
open Compiler.Proofs.IRGeneration
open Compiler.Keccak.MemorySlice (wordToBytesBE)
open Verity.Core (Uint256)
open Compiler.Yul (YulExpr YulStmt)
open Compiler.Modules.Hashing (eip712DigestExpectedYul)

/-! ## Byte-level layout -/

/-- The word stored by `mstore(p, shl(240, 0x1901))`. -/
def eip712PrefixValue : Nat := 0x1901 * 2 ^ 240

/-- Physical memory after the three preimage `mstore`s at `p`, `p + 2`, `p + 34`. -/
def eip712LayoutMemory (m : Memory) (p : Nat) (ds sh : Uint256) : Memory :=
  ((m.writeWord p (valueWord (Uint256.ofNat eip712PrefixValue))).writeWord (p + 2)
    (valueWord ds)).writeWord (p + 34) (valueWord sh)

/-- The 66 EIP-712 preimage bytes `0x19 ‖ 0x01 ‖ domainSeparator ‖ structHash`. -/
def eip712PreimageBytes (ds sh : Uint256) : List Byte :=
  [0x19, 0x01] ++ List.ofFn (valueWord ds) ++ List.ofFn (valueWord sh)

/-- The EIP-712 preimage as the byte array the in-tree Keccak hashes. -/
def eip712Preimage (ds sh : Uint256) : ByteArray :=
  ⟨#[0x19, 0x01]⟩ ++ wordToBytesBE ds.val ++ wordToBytesBE sh.val

/-- Slices split at any length. -/
theorem slice_add (m : Memory) (q a b : Nat) :
    m.slice q (a + b) = m.slice q a ++ m.slice (q + a) b := by
  simp only [Memory.slice, List.range_add, List.map_append, List.map_map]
  congr 1
  apply List.map_congr_left
  intro j _
  simp only [Function.comp_apply, Nat.add_assoc]

/-- A 32-byte slice whose bytes are those of `w` is `w`. -/
theorem slice_eq_ofFn (m : Memory) (q : Nat) (w : Word)
    (h : ∀ j : Fin 32, m.readByte (q + j.val) = w j) :
    m.slice q 32 = List.ofFn w := by
  apply List.ext_getElem (by simp only [Memory.slice, List.length_map, List.length_range,
    List.length_ofFn])
  intro i h1 _
  have hi : i < 32 := by simpa only [Memory.slice, List.length_map, List.length_range] using h1
  simp only [Memory.slice, List.getElem_map, List.getElem_range, List.getElem_ofFn]
  exact h ⟨i, hi⟩

/-- A slice disjoint from a word write is unchanged by it. -/
theorem slice_writeWord_outside (m : Memory) (o : Nat) (w : Word) (q n : Nat)
    (h : q + n ≤ o ∨ o + 32 ≤ q) :
    (m.writeWord o w).slice q n = m.slice q n := by
  simp only [Memory.slice]
  apply List.map_congr_left
  intro j hj
  have := List.mem_range.mp hj
  exact Memory.readByte_writeWord_outside m o w (q + j) (by omega)

/-- Bytes `p` and `p + 1` survive the two later writes. -/
theorem readByte_eip712LayoutMemory_prefix (m : Memory) (p : Nat) (ds sh : Uint256)
    (j : Fin 32) (hj : j.val < 2) :
    (eip712LayoutMemory m p ds sh).readByte (p + j.val) =
      valueWord (Uint256.ofNat eip712PrefixValue) j := by
  unfold eip712LayoutMemory
  rw [Memory.readByte_writeWord_outside _ _ _ _ (by omega),
    Memory.readByte_writeWord_outside _ _ _ _ (by omega), Memory.readByte_writeWord_at]

/-- Bytes `p + 2 … p + 33` are `domainSeparator`; the `structHash` write starts after them. -/
theorem readByte_eip712LayoutMemory_domain (m : Memory) (p : Nat) (ds sh : Uint256)
    (j : Fin 32) :
    (eip712LayoutMemory m p ds sh).readByte (p + 2 + j.val) = valueWord ds j := by
  have := j.isLt
  unfold eip712LayoutMemory
  rw [Memory.readByte_writeWord_outside _ _ _ _ (by omega), Memory.readByte_writeWord_at]

/-- The two prefix bytes are `0x19 0x01`. -/
theorem slice_eip712LayoutMemory_prefix (m : Memory) (p : Nat) (ds sh : Uint256) :
    (eip712LayoutMemory m p ds sh).slice p 2 = [0x19, 0x01] := by
  have h0 := readByte_eip712LayoutMemory_prefix m p ds sh ⟨0, by decide⟩ (by decide)
  have h1 := readByte_eip712LayoutMemory_prefix m p ds sh ⟨1, by decide⟩ (by decide)
  simp only [Nat.add_zero] at h0
  simp only [Memory.slice, List.range_succ, List.range_zero, List.nil_append, List.map_cons,
    List.map_nil, List.cons_append, Nat.add_zero, h0, h1]
  decide

/-- **Byte layout**: the 66 bytes at `p` after the three preimage writes are
`0x19 ‖ 0x01 ‖ BE32 ds ‖ BE32 sh`. -/
theorem slice_eip712LayoutMemory (m : Memory) (p : Nat) (ds sh : Uint256) :
    (eip712LayoutMemory m p ds sh).slice p 66 = eip712PreimageBytes ds sh := by
  rw [show (66 : Nat) = 2 + 32 + 32 from rfl, slice_add, slice_add,
    slice_eip712LayoutMemory_prefix]
  rw [slice_eq_ofFn _ _ _ (readByte_eip712LayoutMemory_domain m p ds sh)]
  rw [show p + (2 + 32) = p + 34 by omega, eip712LayoutMemory,
    slice_eq_ofFn _ _ _ (Memory.readByte_writeWord_at _ _ _)]
  rfl

/-! ## The IR word view of the layout -/

/-- Byte to `UInt8`. -/
def toUInt8 (b : Byte) : UInt8 := UInt8.ofNat b.val

/-- `wordToBytesBE` of a word is its `valueWord` bytes. -/
theorem wordToBytesBE_toList (v : Uint256) :
    (wordToBytesBE v.val).data.toList = (List.ofFn (valueWord v)).map toUInt8 := by
  apply List.ext_getElem (by simp [wordToBytesBE])
  intro i h1 _
  have hi : i < 32 := by simpa [wordToBytesBE] using h1
  simp only [wordToBytesBE, List.getElem_map, List.getElem_range, List.getElem_ofFn,
    valueWord, toUInt8]

/-- The serialized word of the IR word view at `q` is the 32 physical bytes at `q`. -/
theorem irWordToBytesBE_wordValue (m : Memory) (q : Nat) :
    (irWordToBytesBE (wordValue (m.readWord q)).val).data.toList =
      (m.slice q 32).map toUInt8 := by
  rw [slice_eq_ofFn m q (m.readWord q) (fun _ => rfl)]
  have := wordToBytesBE_toList (wordValue (m.readWord q))
  rwa [valueWord_wordValue] at this

/-- **Lift**: `keccak256(p, 66)`'s input over the IR word view of a physical memory is
the 66 physical bytes at `p`, as long as the three words read do not wrap. -/
theorem irMemorySliceBytesBE_physical (m : Memory) (p : Nat)
    (hp : p + 64 < Compiler.Constants.evmModulus) :
    (irMemorySliceBytesBE (fun q => (wordValue (m.readWord q)).val) p 66).data.toList =
      (m.slice p 66).map toUInt8 := by
  have h96 : m.slice p 96 = m.slice p 32 ++ m.slice (p + 32) 32 ++ m.slice (p + 64) 32 := by
    rw [show (96 : Nat) = 32 + 32 + 32 from rfl, slice_add, slice_add]
  have h66 : (m.slice p 96).take 66 = m.slice p 66 := by
    rw [show (96 : Nat) = 66 + 30 from rfl, slice_add]
    exact List.take_left' (by simp [Memory.slice])
  have hw : memorySliceWords (fun q => (wordValue (m.readWord q)).val) p 66 =
      [(wordValue (m.readWord p)).val, (wordValue (m.readWord (p + 32))).val,
        (wordValue (m.readWord (p + 64))).val] := by
    simp [memorySliceWords, byteWordCount, List.range_succ,
      Nat.mod_eq_of_lt (show p < Compiler.Constants.evmModulus by omega),
      Nat.mod_eq_of_lt (show p + 32 < Compiler.Constants.evmModulus by omega),
      Nat.mod_eq_of_lt hp]
  rw [← h66, List.map_take, h96]
  simp only [irMemorySliceBytesBE, hw, List.foldl_cons, List.foldl_nil, ByteArray.data_extract,
    ByteArray.data_append, Array.toList_extract]
  simp [irWordToBytesBE_wordValue]

/-! ## The Keccak preimage -/

/-- `eip712Preimage` is `eip712PreimageBytes` as `UInt8`s. -/
theorem eip712Preimage_toList (ds sh : Uint256) :
    (eip712Preimage ds sh).data.toList = (eip712PreimageBytes ds sh).map toUInt8 := by
  simp only [eip712Preimage, eip712PreimageBytes, ByteArray.data_append, Array.toList_append,
    wordToBytesBE_toList, List.map_append]
  rfl

/-- If the 66 physical bytes at `p` are the EIP-712 preimage, the bytes `keccak256(p, 66)`
reads from the IR word view are `eip712Preimage ds sh`. -/
theorem irMemorySliceBytesBE_eip712 (m : Memory) (p : Nat) (ds sh : Uint256)
    (hp : p + 64 < Compiler.Constants.evmModulus)
    (hslice : m.slice p 66 = eip712PreimageBytes ds sh) :
    irMemorySliceBytesBE (fun q => (wordValue (m.readWord q)).val) p 66 =
      eip712Preimage ds sh := by
  apply ByteArray.ext
  apply Array.toList_inj.mp
  rw [irMemorySliceBytesBE_physical m p hp, hslice, eip712Preimage_toList]

/-- The EIP-712 digest: Keccak-256 of `0x19 ‖ 0x01 ‖ domainSeparator ‖ structHash`. -/
def eip712DigestValue (ds sh : Uint256) : Nat :=
  KeccakEngine.byteArrayToNatBE (KeccakEngine.keccak256 (eip712Preimage ds sh)) %
    Compiler.Constants.evmModulus

/-- **Keccak preimage**: `keccak256(p, 66)` over such a memory is `eip712DigestValue ds sh`. -/
theorem abstractKeccakMemorySlice_eip712 (m : Memory) (p : Nat) (ds sh : Uint256)
    (hp : p + 64 < Compiler.Constants.evmModulus)
    (hslice : m.slice p 66 = eip712PreimageBytes ds sh) :
    abstractKeccakMemorySlice (fun q => (wordValue (m.readWord q)).val) p 66 =
      eip712DigestValue ds sh := by
  rw [abstractKeccakMemorySlice, irMemorySliceBytesBE_eip712 m p ds sh hp hslice]
  rfl

/-! ## Executing the emitted Yul -/

/-- The pointer temporary of `eip712DigestExpectedYul`. -/
def eip712PtrName : String := "__digest_eip712_ptr"

/-- State after the five scratch statements of `eip712DigestExpectedYul`'s block. -/
def eip712ScratchState (s : IRState) (p : Nat) (ds sh : Uint256) : IRState :=
  (((((s.setVar "digest" 0).setVar eip712PtrName p).writePhysicalMemoryValue p
    eip712PrefixValue).writePhysicalMemoryValue (p + 2) ds.val).writePhysicalMemoryValue
    (p + 34) sh.val).writePhysicalMemoryValue 64 (p + 96)

/-- State after executing `eip712DigestExpectedYul`. -/
def eip712FinalState (s : IRState) (p : Nat) (ds sh : Uint256) : IRState :=
  let scratch := eip712ScratchState s p ds sh
  scratch.setVar "digest" (abstractKeccakMemorySlice scratch.memory p 66)

/-- `let name := e` binds the value of `e`. -/
theorem execIRStmt_let_of_eval {fuel : Nat} {s : IRState} {name : String} {e : YulExpr}
    {v : Nat} (h : evalIRExpr s e = some v) :
    execIRStmt (fuel + 1) s (.let_ name e) = .continue (s.setVar name v) := by
  simp [execIRStmt, h]

/-- `name := e` binds the value of `e`. -/
theorem execIRStmt_assign_of_eval {fuel : Nat} {s : IRState} {name : String} {e : YulExpr}
    {v : Nat} (h : evalIRExpr s e = some v) :
    execIRStmt (fuel + 1) s (.assign name e) = .continue (s.setVar name v) := by
  simp [execIRStmt, h]

/-- `mstore(a, b)` writes the value of `b` at the (word-normalized) value of `a`. -/
theorem execIRStmt_mstore_of_eval {fuel : Nat} {s : IRState} {a b : YulExpr} {o v : Nat}
    (ho : evalIRExpr s a = some o) (hv : evalIRExpr s b = some v) :
    execIRStmt (fuel + 1) s (.exprStmt (.call "mstore" [a, b])) =
      .continue (s.writePhysicalMemoryValue (Uint256.ofNat o).val v) := by
  simp [execIRStmt, ho, hv]

/-- `add(a, k)` wraps modulo `2^256`. -/
theorem evalIRExpr_add_lit {s : IRState} {a : YulExpr} {x : Nat} (k : Nat)
    (h : evalIRExpr s a = some x) :
    evalIRExpr s (.call "add" [a, .lit k]) = some ((x + k) % Compiler.Constants.evmModulus) := by
  simp [evalIRExpr, evalIRCall, evalIRExprs, h,
    Compiler.Proofs.YulGeneration.Backends.evalBuiltinCallWithEvmYulLeanContext,
    Compiler.Proofs.YulGeneration.Backends.evalBuiltinCallViaEvmYulLean]

/-- `shl(240, 0x1901)` is `eip712PrefixValue`. -/
theorem evalIRExpr_eip712Prefix (s : IRState) :
    evalIRExpr s (.call "shl" [.lit 240, .hex 0x1901]) = some eip712PrefixValue := by
  simp [evalIRExpr, evalIRCall, evalIRExprs,
    Compiler.Proofs.YulGeneration.Backends.evalBuiltinCallWithEvmYulLeanContext,
    Compiler.Proofs.YulGeneration.Backends.evalBuiltinCallViaEvmYulLean]
  decide

/-- `Uint256.ofNat` is the identity on in-range values. -/
theorem uint256_ofNat_val (x : Uint256) : Uint256.ofNat x.val = x :=
  Uint256.ext (Nat.mod_eq_of_lt x.isLt)

/-- A word-sized offset is unchanged by `Uint256.ofNat`. -/
theorem val_ofNat_of_lt {q : Nat} (h : q < Compiler.Constants.evmModulus) :
    (Uint256.ofNat q).val = q :=
  Nat.mod_eq_of_lt h

/-- Memory writes leave variables unchanged. -/
@[simp] theorem getVar_writePhysicalMemoryValue (s : IRState) (o v : Nat) (name : String) :
    (s.writePhysicalMemoryValue o v).getVar name = s.getVar name := rfl

/-- The statements inside `eip712DigestExpectedYul`'s block, with literals spelled out. -/
def eip712DigestBlockBody : List YulStmt :=
  let ptr := YulExpr.ident eip712PtrName
  [ .let_ eip712PtrName (.call "mload" [.lit 64])
  , .exprStmt (.call "mstore" [ptr, .call "shl" [.lit 240, .hex 0x1901]])
  , .exprStmt (.call "mstore" [.call "add" [ptr, .lit 2], .ident "domainSeparator"])
  , .exprStmt (.call "mstore" [.call "add" [ptr, .lit 34], .ident "structHash"])
  , .exprStmt (.call "mstore" [.lit 64, .call "add" [ptr, .lit 96]])
  , .assign "digest" (.call "keccak256" [ptr, .lit 66]) ]

/-- `eip712DigestExpectedYul` is `digest := 0` followed by `eip712DigestBlockBody`. -/
theorem eip712DigestExpectedYul_eq_block :
    eip712DigestExpectedYul =
      [.let_ "digest" (.lit 0), .block eip712DigestBlockBody] := rfl

/-- One `continue` statement followed by nothing. -/
theorem execIRStmts_singleton_of_continue (fuel : Nat) (s next : IRState) (stmt : YulStmt)
    (h : execIRStmt fuel s stmt = .continue next) :
    execIRStmts (fuel + 1) s [stmt] = .continue next := by
  rw [execIRStmts_succ_cons_of_continue _ _ _ _ _ h]
  simp

/-- `mstore(add(ptr, k), name)` writes the bound word at `p + k`. -/
theorem execIRStmt_mstore_ptr_add (fuel : Nat) (t : IRState) (p k v : Nat) (name : String)
    (hptr : t.getVar eip712PtrName = some p) (hv : t.getVar name = some v)
    (hk : p + k < Compiler.Constants.evmModulus) :
    execIRStmt (fuel + 1) t
        (.exprStmt (.call "mstore" [.call "add" [.ident eip712PtrName, .lit k], .ident name])) =
      .continue (t.writePhysicalMemoryValue (p + k) v) := by
  rw [execIRStmt_mstore_of_eval (evalIRExpr_add_lit k (by simpa using hptr)) (by simpa using hv),
    Nat.mod_eq_of_lt hk, val_ofNat_of_lt hk]

/-- `mstore(ptr, shl(240, 0x1901))` writes the `0x1901` prefix word at `p`. -/
theorem execIRStmt_mstore_eip712Prefix (fuel : Nat) (t : IRState) (p : Nat)
    (hptr : t.getVar eip712PtrName = some p) (hp : p < Compiler.Constants.evmModulus) :
    execIRStmt (fuel + 1) t
        (.exprStmt (.call "mstore" [.ident eip712PtrName, .call "shl" [.lit 240, .hex 0x1901]])) =
      .continue (t.writePhysicalMemoryValue p eip712PrefixValue) := by
  rw [execIRStmt_mstore_of_eval (by simpa using hptr) (evalIRExpr_eip712Prefix t),
    val_ofNat_of_lt hp]

/-- `mstore(0x40, add(ptr, 96))` bumps the free pointer. -/
theorem execIRStmt_mstore_eip712FreePointer (fuel : Nat) (t : IRState) (p : Nat)
    (hptr : t.getVar eip712PtrName = some p) (hp : p + 96 < Compiler.Constants.evmModulus) :
    execIRStmt (fuel + 1) t
        (.exprStmt (.call "mstore" [.lit 64, .call "add" [.ident eip712PtrName, .lit 96]])) =
      .continue (t.writePhysicalMemoryValue 64 (p + 96)) := by
  rw [execIRStmt_mstore_of_eval (show evalIRExpr t (.lit 64) = some 64 by simp)
    (evalIRExpr_add_lit 96 (by simpa using hptr)), Nat.mod_eq_of_lt hp,
    val_ofNat_of_lt (show 64 < Compiler.Constants.evmModulus by omega)]

/-- `digest := keccak256(ptr, 66)` binds the memory-slice Keccak at `p`. -/
theorem execIRStmt_assign_eip712Keccak (fuel : Nat) (t : IRState) (p : Nat)
    (hptr : t.getVar eip712PtrName = some p) :
    execIRStmt (fuel + 1) t (.assign "digest" (.call "keccak256" [.ident eip712PtrName, .lit 66])) =
      .continue (t.setVar "digest" (abstractKeccakMemorySlice t.memory p 66)) :=
  execIRStmt_assign_of_eval (by simp [evalIRExpr, evalIRCall, evalIRExprs, hptr])

/-- After the pointer is bound, the block's stores and hash run to `eip712FinalState`. -/
theorem execIRStmts_eip712DigestBlockBody_tail (fuel : Nat) (s : IRState) (p : Nat)
    (ds sh : Uint256) (hp : p + 96 < Compiler.Constants.evmModulus)
    (hptr : ((s.setVar "digest" 0).setVar eip712PtrName p).getVar eip712PtrName = some p)
    (hds : ((s.setVar "digest" 0).setVar eip712PtrName p).getVar "domainSeparator" = some ds.val)
    (hsh : ((s.setVar "digest" 0).setVar eip712PtrName p).getVar "structHash" = some sh.val) :
    execIRStmts (fuel + 6) ((s.setVar "digest" 0).setVar eip712PtrName p)
        eip712DigestBlockBody.tail =
      .continue (eip712FinalState s p ds sh) := by
  let s3 := ((s.setVar "digest" 0).setVar eip712PtrName p).writePhysicalMemoryValue p
    eip712PrefixValue
  let s4 := s3.writePhysicalMemoryValue (p + 2) ds.val
  let s5 := s4.writePhysicalMemoryValue (p + 34) sh.val
  let s6 := s5.writePhysicalMemoryValue 64 (p + 96)
  simp only [eip712DigestBlockBody, List.tail_cons]
  rw [execIRStmts_succ_cons_of_continue _ _ _ _ _
      (execIRStmt_mstore_eip712Prefix (fuel + 4) _ p hptr (by omega)),
    execIRStmts_succ_cons_of_continue _ _ _ _ _
      (execIRStmt_mstore_ptr_add (fuel + 3) s3 p 2 _ _ hptr hds (by omega)),
    execIRStmts_succ_cons_of_continue _ _ _ _ _
      (execIRStmt_mstore_ptr_add (fuel + 2) s4 p 34 _ _ hptr hsh (by omega)),
    execIRStmts_succ_cons_of_continue _ _ _ _ _
      (execIRStmt_mstore_eip712FreePointer (fuel + 1) s5 p hptr hp),
    execIRStmts_singleton_of_continue _ _ _ _ (execIRStmt_assign_eip712Keccak fuel s6 p hptr)]
  rfl

/-- The block body binds the pointer from the free-memory slot, then runs the tail. -/
theorem execIRStmts_eip712DigestBlockBody (fuel : Nat) (s : IRState) (p : Nat)
    (ds sh : Uint256) (hfp : s.memory 64 = p)
    (hds : s.getVar "domainSeparator" = some ds.val)
    (hsh : s.getVar "structHash" = some sh.val)
    (hp : p + 96 < Compiler.Constants.evmModulus) :
    execIRStmts (fuel + 7) (s.setVar "digest" 0) eip712DigestBlockBody =
      .continue (eip712FinalState s p ds sh) := by
  have hlet := execIRStmt_let_of_eval (fuel := fuel + 5) (name := eip712PtrName)
    (show evalIRExpr (s.setVar "digest" 0) (.call "mload" [.lit 64]) = some p by
      simp [evalIRExpr, evalIRCall_mload_singleton, hfp])
  have hne : ∀ x, x ≠ eip712PtrName → x ≠ "digest" →
      ((s.setVar "digest" 0).setVar eip712PtrName p).getVar x = s.getVar x := by
    intro x h1 h2
    rw [IRState.getVar_setVar_ne _ _ h1, IRState.getVar_setVar_ne _ _ h2]
  rw [show eip712DigestBlockBody = _ :: eip712DigestBlockBody.tail from rfl,
    execIRStmts_succ_cons_of_continue _ _ _ _ _ hlet]
  exact execIRStmts_eip712DigestBlockBody_tail fuel s p ds sh hp
    (IRState.getVar_setVar_same _ _ _) (by rw [hne _ (by decide) (by decide), hds])
    (by rw [hne _ (by decide) (by decide), hsh])

/-- Executing `eip712DigestExpectedYul` from a state with free pointer `p` reaches
`eip712FinalState`. -/
theorem execIRStmts_eip712DigestExpectedYul (fuel : Nat) (s : IRState) (p : Nat)
    (ds sh : Uint256) (hfp : s.memory 64 = p)
    (hds : s.getVar "domainSeparator" = some ds.val)
    (hsh : s.getVar "structHash" = some sh.val)
    (hp : p + 96 < Compiler.Constants.evmModulus) :
    execIRStmts (fuel + 10) s eip712DigestExpectedYul =
      .continue (eip712FinalState s p ds sh) := by
  have hzero : evalIRExpr s (.lit 0) = some 0 := by simp
  have hblock : execIRStmt (fuel + 8) (s.setVar "digest" 0) (.block eip712DigestBlockBody) =
      .continue (eip712FinalState s p ds sh) := by
    simp only [execIRStmt]
    exact execIRStmts_eip712DigestBlockBody fuel s p ds sh hfp hds hsh hp
  rw [eip712DigestExpectedYul_eq_block,
    execIRStmts_succ_cons_of_continue _ _ _ _ _ (execIRStmt_let_of_eval (fuel := fuel + 8) hzero),
    execIRStmts_singleton_of_continue _ _ _ _ hblock]

/-- The scratch writes leave the EIP-712 preimage at `p`; the free-pointer bump at `0x40`
does not touch it because `96 ≤ p`. -/
theorem slice_eip712ScratchState (s : IRState) (p : Nat) (ds sh : Uint256) (hlow : 96 ≤ p) :
    (eip712ScratchState s p ds sh).byteMemory.slice p 66 = eip712PreimageBytes ds sh := by
  have h : (eip712ScratchState s p ds sh).byteMemory =
      (eip712LayoutMemory s.byteMemory p (Uint256.ofNat ds.val) (Uint256.ofNat sh.val)).writeWord
        64 (valueWord (Uint256.ofNat (p + 96))) := rfl
  rw [uint256_ofNat_val, uint256_ofNat_val] at h
  rw [h, slice_writeWord_outside _ _ _ _ _ (by omega), slice_eip712LayoutMemory]

/-- **EIP-712 preimage layout**: executing the emitted `eip712Digest` Yul from a state whose
free pointer `p` satisfies `96 ≤ p` and `p + 96 < 2^256`, with `domainSeparator = ds` and
`structHash = sh` bound, continues; the 66 bytes `keccak256(p, 66)` reads are exactly
`0x19 ‖ 0x01 ‖ BE32 ds ‖ BE32 sh`, and `digest` is their Keccak-256. -/
theorem eip712Digest_preimage_layout (fuel : Nat) (s : IRState) (p : Nat) (ds sh : Uint256)
    (hfp : s.memory 64 = p) (hds : s.getVar "domainSeparator" = some ds.val)
    (hsh : s.getVar "structHash" = some sh.val) (hlow : 96 ≤ p)
    (hp : p + 96 < Compiler.Constants.evmModulus) :
    ∃ s', execIRStmts (fuel + 10) s eip712DigestExpectedYul = .continue s' ∧
      irMemorySliceBytesBE s'.memory p 66 = eip712Preimage ds sh ∧
      s'.getVar "digest" = some (eip712DigestValue ds sh) := by
  have hslice := slice_eip712ScratchState s p ds sh hlow
  refine ⟨_, execIRStmts_eip712DigestExpectedYul fuel s p ds sh hfp hds hsh hp, ?_, ?_⟩
  · exact irMemorySliceBytesBE_eip712 _ p ds sh (by omega) hslice
  · rw [eip712FinalState, IRState.getVar_setVar_same]
    exact congrArg some (abstractKeccakMemorySlice_eip712 _ p ds sh (by omega) hslice)

end Compiler.Proofs.Eip712DigestLayout
