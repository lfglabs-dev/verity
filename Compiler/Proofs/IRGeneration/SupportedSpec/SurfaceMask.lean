import Compiler.Proofs.IRGeneration.ExprCore

namespace Compiler.Proofs.IRGeneration

open Compiler
open Compiler.CompilationModel

/-!
# Single-Pass $\mathcal{O}(|AST|)$ `SurfaceMask` Bitset Algebra (Node R1)

This module replaces repeated constructor-by-constructor boolean walks over
`CompilationModel.Expr` and `CompilationModel.Stmt` with a single-pass
catamorphism into a 32-bit capability mask (`SurfaceMask := UInt32`).

Each surface family occupies a dedicated bit position (`bitCoreGap` through
`bitMulDiv512`). The catamorphism computes the bitwise union (`|||`) of all
touched surface families in $\mathcal{O}(|AST|)$ time, and satisfies boolean
distributivity (`hasMask_or`, `maskSubset_or`) and monotonicity under mask
inclusion (`maskSubset_mono`).
-/

/-- 32-bit bitset encoding the union of language surfaces touched by an AST node. -/
abbrev SurfaceMask := UInt32

/-- Bit 0: Core expression or statement forms outside the base induction fragment. -/
def bitCoreGap : SurfaceMask := (1 : UInt32) <<< 0

/-- Bit 1: Storage or mapping state-read expressions (`sload` / slot hashing). -/
def bitStateRead : SurfaceMask := (1 : UInt32) <<< 1

/-- Bit 2: Singleton mapping or struct-member storage writes (`sstore` at hashed slot). -/
def bitMappingWrite : SurfaceMask := (1 : UInt32) <<< 2

/-- Bit 3: Direct or expression-position internal helper calls. -/
def bitInternalCall : SurfaceMask := (1 : UInt32) <<< 3

/-- Bit 4: Linked foreign calls, external call binds, and External Call Modules (`Stmt.ecm`). -/
def bitExternalCall : SurfaceMask := (1 : UInt32) <<< 4

/-- Bit 5: Low-level EVM call/code/memory mechanics (`call`, `staticcall`, `delegatecall`, `returnCodeData`). -/
def bitLowLevelMem : SurfaceMask := (1 : UInt32) <<< 5

/-- Bit 6: Contract event emission (`Stmt.emit`). -/
def bitEventEmit : SurfaceMask := (1 : UInt32) <<< 6

/-- Bit 7: Raw calldata reads disallowed in constructor deploy bodies (`calldataload`, `calldatasize`, `calldatacopy`). -/
def bitConstructorRaw : SurfaceMask := (1 : UInt32) <<< 7

/-- Bit 8: Algebraic data type construction, projection, and pattern matching (`matchAdt`). -/
def bitAdtSurface : SurfaceMask := (1 : UInt32) <<< 8

/-- Bit 9: Inline or unsafe Yul escape hatches (`unsafeBlock`, `unsafeYul`). -/
def bitInlineYul : SurfaceMask := (1 : UInt32) <<< 9

/-- Bit 10: Dynamic storage arrays (`storageArrayLength`, `storageArrayElement`, `storageArrayPush`, `storageArrayPop`). -/
def bitStorageArray : SurfaceMask := (1 : UInt32) <<< 10

/-- Bit 11: Bitmap set-bit iteration (`Stmt.forEachSetBit`). -/
def bitForEachSetBit : SurfaceMask := (1 : UInt32) <<< 11

/-- Bit 12: Full-precision 512-bit multiply-divide (`mulDiv512Down`, `mulDiv512Up`). -/
def bitMulDiv512 : SurfaceMask := (1 : UInt32) <<< 12

/-- Test whether any bit of `mask` is set in `m`. -/
def hasMask (m mask : SurfaceMask) : Bool :=
  (m &&& mask) != 0

/-- Test whether every set bit of `m` is permitted by `allowed`. -/
def maskSubset (m allowed : SurfaceMask) : Bool :=
  (m &&& allowed) == m

mutual
/-- Single-pass $\mathcal{O}(|e|)$ catamorphism computing the union of all
surface bits touched by an expression `e`. -/
def exprSurfaceMask : Expr → SurfaceMask
  | .literal _ | .param _ | .caller | .contractAddress | .txOrigin
  | .chainid | .msgValue | .blockTimestamp | .blockNumber
  | .blobbasefee | .returndataSize | .localVar _ | .constructorArg _ => 0
  | .calldatasize | .arrayLength _ | .dynamicBytesEq _ _ => bitConstructorRaw
  | .calldataload a | .arrayElement _ a =>
      bitConstructorRaw ||| exprSurfaceMask a
  | .immutable _ | .selfBalance | .baseFee | .gasPrice
  | .memoryArrayLength _
  | .paramDynamicHeadWord _ _ | .paramDynamicStaticComposite _ _
  | .paramDynamicMemberLength _ _ | .paramDynamicMemberDataOffset _ _ =>
      bitCoreGap
  | .memoryArrayElement _ b | .arrayElementWord _ b _ _
  | .arrayElementDynamicWord _ b _ | .arrayElementDynamicDataOffset _ b
  | .arrayElementDynamicMemberLength _ b _
  | .arrayElementDynamicMemberDataOffset _ b _
  | .paramDynamicMemberElement _ _ b =>
      bitCoreGap ||| exprSurfaceMask b
  | .arrayElementDynamicMemberElement _ a _ b =>
      bitCoreGap ||| exprSurfaceMask a ||| exprSurfaceMask b
  | .forkIfAtLeast _ t e =>
      bitCoreGap ||| exprSurfaceMask t ||| exprSurfaceMask e
  | .intrinsic _ _ _ args =>
      bitCoreGap ||| bitConstructorRaw ||| exprListSurfaceMask args
  | .storage _ | .storageAddr _ => bitStateRead
  | .mapping _ k | .mappingWord _ k _ | .mappingPackedWord _ k _ _
  | .mappingUint _ k | .structMember _ k _ =>
      bitCoreGap ||| bitStateRead ||| exprSurfaceMask k
  | .mapping2 _ k1 k2 | .mapping2Word _ k1 k2 _ | .structMember2 _ k1 k2 _ =>
      bitCoreGap ||| bitStateRead ||| exprSurfaceMask k1 ||| exprSurfaceMask k2
  | .mappingChain _ keys =>
      bitCoreGap ||| bitStateRead ||| exprListSurfaceMask keys
  | .storageArrayLength _ =>
      bitCoreGap ||| bitStateRead ||| bitStorageArray
  | .storageArrayElement _ idx =>
      bitCoreGap ||| bitStateRead ||| bitStorageArray ||| exprSurfaceMask idx
  | .internalCall _ args =>
      bitCoreGap ||| bitInternalCall ||| exprListSurfaceMask args
  | .externalCall name [base, exponent] =>
      if name == builtinExpName then
        exprSurfaceMask base ||| exprSurfaceMask exponent
      else
        bitCoreGap ||| bitExternalCall ||| exprSurfaceMask base ||| exprSurfaceMask exponent
  | .externalCall _ args =>
      bitCoreGap ||| bitExternalCall ||| exprListSurfaceMask args
  | .mload a | .tload a | .extcodesize a | .returndataOptionalBoolAt a =>
      exprSurfaceMask a
  | .keccak256 a b =>
      exprSurfaceMask a ||| exprSurfaceMask b
  | .call g t v io is oo os =>
      bitCoreGap ||| bitLowLevelMem |||
        exprSurfaceMask g ||| exprSurfaceMask t ||| exprSurfaceMask v |||
        exprSurfaceMask io ||| exprSurfaceMask is ||| exprSurfaceMask oo |||
        exprSurfaceMask os
  | .staticcall g t io is oo os | .delegatecall g t io is oo os =>
      bitCoreGap ||| bitLowLevelMem |||
        exprSurfaceMask g ||| exprSurfaceMask t |||
        exprSurfaceMask io ||| exprSurfaceMask is ||| exprSurfaceMask oo |||
        exprSurfaceMask os
  | .mulDiv512Down a b c | .mulDiv512Up a b c =>
      bitCoreGap ||| bitMulDiv512 |||
        exprSurfaceMask a ||| exprSurfaceMask b ||| exprSurfaceMask c
  | .adtConstruct _ _ args =>
      bitCoreGap ||| bitStateRead ||| bitAdtSurface ||| exprListSurfaceMask args
  | .adtTag _ _ | .adtField _ _ _ _ _ =>
      bitCoreGap ||| bitStateRead ||| bitAdtSurface
  | .bitNot a | .logicalNot a =>
      exprSurfaceMask a
  | .add a b | .sub a b | .mul a b | .div a b | .sdiv a b | .mod a b | .smod a b
  | .bitAnd a b | .bitOr a b | .bitXor a b | .shl a b | .shr a b | .sar a b
  | .byte a b | .signextend a b | .eq a b | .ge a b | .gt a b | .sgt a b
  | .lt a b | .slt a b | .le a b | .logicalAnd a b | .logicalOr a b
  | .ceilDiv a b | .wMulDown a b | .wDivUp a b | .min a b | .max a b =>
      exprSurfaceMask a ||| exprSurfaceMask b
  | .mulDivDown a b c | .mulDivUp a b c | .ite a b c =>
      exprSurfaceMask a ||| exprSurfaceMask b ||| exprSurfaceMask c

/-- Single-pass surface mask over a list of expressions. -/
def exprListSurfaceMask : List Expr → SurfaceMask
  | [] => 0
  | e :: es => exprSurfaceMask e ||| exprListSurfaceMask es
end

mutual
/-- Single-pass $\mathcal{O}(|s|)$ catamorphism computing the union of all
surface bits touched by a statement `s`. -/
def stmtSurfaceMask : Stmt → SurfaceMask
  | .letVar _ v | .assignVar _ v | .setStorage _ v | .setStorageAddr _ v
  | .require v _ | .return v =>
      exprSurfaceMask v
  | .setImmutable _ v | .setStorageWord _ _ v | .panicCode v =>
      bitCoreGap ||| exprSurfaceMask v
  | .panic _ | .returnArray _ | .returnBytes _ | .returnStorageWords _ =>
      bitCoreGap
  | .mstore o v | .tstore o v =>
      exprSurfaceMask o ||| exprSurfaceMask v
  | .calldatacopy d s sz =>
      bitConstructorRaw ||| exprSurfaceMask d ||| exprSurfaceMask s ||| exprSurfaceMask sz
  | .returndataCopy d s sz =>
      exprSurfaceMask d ||| exprSurfaceMask s ||| exprSurfaceMask sz
  | .stop | .revertEmpty | .revertReturndata => 0
  | .setMapping _ k v | .setMappingWord _ k _ v
  | .setMappingPackedWord _ k _ _ v | .setMappingUint _ k v
  | .setStructMember _ k _ v =>
      bitMappingWrite ||| exprSurfaceMask k ||| exprSurfaceMask v
  | .setMapping2 _ k1 k2 v | .setMapping2Word _ k1 k2 _ v
  | .setStructMember2 _ k1 k2 _ v =>
      bitMappingWrite ||| exprSurfaceMask k1 ||| exprSurfaceMask k2 ||| exprSurfaceMask v
  | .setMappingChain _ keys v =>
      bitMappingWrite ||| exprListSurfaceMask keys ||| exprSurfaceMask v
  | .storageArrayPush _ v =>
      bitStorageArray ||| exprSurfaceMask v
  | .storageArrayPop _ =>
      bitStorageArray
  | .setStorageArrayElement _ idx v =>
      bitStorageArray ||| exprSurfaceMask idx ||| exprSurfaceMask v
  | .emit _ args =>
      bitEventEmit ||| exprListSurfaceMask args
  | .internalCall _ args | .internalCallAssign _ _ args =>
      bitInternalCall ||| exprListSurfaceMask args
  | .externalCallBind _ _ args | .tryExternalCallBind _ _ _ args | .ecm _ args =>
      bitExternalCall ||| exprListSurfaceMask args
  | .returnCodeData ptr =>
      bitLowLevelMem ||| exprSurfaceMask ptr
  | .rawLog topics dOff dSz =>
      bitCoreGap ||| exprListSurfaceMask topics ||| exprSurfaceMask dOff ||| exprSurfaceMask dSz
  | .requireError cond _ args =>
      bitCoreGap ||| exprSurfaceMask cond ||| exprListSurfaceMask args
  | .revertError _ args | .returnValues args =>
      bitCoreGap ||| exprListSurfaceMask args
  | .ite cond thenB elseB =>
      exprSurfaceMask cond ||| stmtListSurfaceMask thenB ||| stmtListSurfaceMask elseB
  | .forEach _ (.literal _) body =>
      stmtListSurfaceMask body
  | .forEach _ count body =>
      bitCoreGap ||| exprSurfaceMask count ||| stmtListSurfaceMask body
  | .forEachSetBit _ count body =>
      bitCoreGap ||| bitForEachSetBit ||| exprSurfaceMask count ||| stmtListSurfaceMask body
  | .unsafeBlock _ body =>
      bitCoreGap ||| bitInlineYul ||| stmtListSurfaceMask body
  | .unsafeYul _ =>
      bitCoreGap ||| bitInlineYul
  | .matchAdt _ scrutinee branches =>
      bitCoreGap ||| bitAdtSurface ||| exprSurfaceMask scrutinee |||
        matchAdtBranchesSurfaceMask branches

/-- Single-pass surface mask over ADT match branches. -/
def matchAdtBranchesSurfaceMask : List (String × List String × List Stmt) → SurfaceMask
  | [] => 0
  | (_, _, body) :: rest => stmtListSurfaceMask body ||| matchAdtBranchesSurfaceMask rest

/-- Single-pass $\mathcal{O}(|\mathit{stmts}|)$ catamorphism computing the union
of all surface bits touched by a statement list. -/
def stmtListSurfaceMask : List Stmt → SurfaceMask
  | [] => 0
  | s :: ss => stmtSurfaceMask s ||| stmtListSurfaceMask ss
end

/-! ## Bitwise & Catamorphism Algebraic Laws -/

private theorem uint32_ext_bitvec {a b : SurfaceMask} (h : a.toBitVec = b.toBitVec) : a = b :=
  UInt32.eq_of_toBitVec_eq h

theorem surfaceMask_and_assoc (a b c : SurfaceMask) :
    a &&& b &&& c = a &&& (b &&& c) := by
  apply uint32_ext_bitvec; ext i hi; simp [Bool.and_assoc]

theorem surfaceMask_or_comm (a b : SurfaceMask) :
    a ||| b = b ||| a := by
  apply uint32_ext_bitvec; ext i hi; simp [Bool.or_comm]

theorem surfaceMask_or_and_distrib_right (a b c : SurfaceMask) :
    (a ||| b) &&& c = (a &&& c) ||| (b &&& c) := by
  apply uint32_ext_bitvec; ext i hi; simp [Bool.and_or_distrib_right]

theorem surfaceMask_and_or_self_left (a b : SurfaceMask) :
    a &&& (a ||| b) = a := by
  apply uint32_ext_bitvec; ext i hi
  simp only [UInt32.toBitVec_and, UInt32.toBitVec_or, BitVec.getElem_and, BitVec.getElem_or,
    Bool.and_or_distrib_left, Bool.and_self, Bool.or_eq_left_iff_imp, Bool.and_eq_true]
  exact And.left

@[simp]
theorem surfaceMask_and_zero (a : SurfaceMask) :
    a &&& (0 : SurfaceMask) = 0 := by
  apply uint32_ext_bitvec; ext i hi; simp

private theorem surfaceMask_or_eq_zero_iff (a b : SurfaceMask) :
    a ||| b = 0 ↔ a = 0 ∧ b = 0 := by
  have bitZero (x : SurfaceMask) (hx : ∀ i (hi : i < 32), x.toBitVec[i] = false) : x = 0 := by
    apply uint32_ext_bitvec; ext i hi; simpa using hx i hi
  constructor
  · intro h
    have hbit : ∀ i (hi : i < 32), a.toBitVec[i] = false ∧ b.toBitVec[i] = false := by
      intro i hi
      have hb := congrArg (fun x => x.toBitVec[i]) h
      simpa [UInt32.toBitVec_or, UInt32.toBitVec_ofNat, BitVec.getElem_or, BitVec.getElem_zero,
        Bool.or_eq_false_iff] using hb
    exact ⟨bitZero a (fun i hi => (hbit i hi).1), bitZero b (fun i hi => (hbit i hi).2)⟩
  · rintro ⟨h1, h2⟩
    rw [h1, h2]; rfl

/-- The empty mask `0` contains no surface bits. -/
@[simp]
theorem hasMask_zero (mask : SurfaceMask) : hasMask 0 mask = false := by
  simp [hasMask]

/-- `hasMask` distributes over bitwise union `|||`. -/
@[simp]
theorem hasMask_or (m₁ m₂ mask : SurfaceMask) :
    hasMask (m₁ ||| m₂) mask = (hasMask m₁ mask || hasMask m₂ mask) := by
  apply Bool.eq_iff_iff.mpr
  simp only [hasMask, bne_iff_ne, ne_eq, Bool.or_eq_true, ← Decidable.not_and_iff_or_not]
  rw [surfaceMask_or_and_distrib_right]
  exact not_congr (surfaceMask_or_eq_zero_iff (m₁ &&& mask) (m₂ &&& mask))

/-- Bitwise union on `SurfaceMask` is associative. -/
theorem surfaceMask_or_assoc (a b c : SurfaceMask) :
    a ||| b ||| c = a ||| (b ||| c) := by
  apply uint32_ext_bitvec; ext i hi; simp [Bool.or_assoc]

/-- Bitwise `0` is the left identity for `|||`. -/
@[simp]
theorem surfaceMask_zero_or (a : SurfaceMask) :
    (0 : SurfaceMask) ||| a = a := by
  apply uint32_ext_bitvec; ext i hi; simp

/-- Bitwise `0` is the right identity for `|||`. -/
@[simp]
theorem surfaceMask_or_zero (a : SurfaceMask) :
    a ||| (0 : SurfaceMask) = a := by
  apply uint32_ext_bitvec; ext i hi; simp

/-- The empty mask `0` is a subset of every allowed mask. -/
@[simp]
theorem maskSubset_zero (allowed : SurfaceMask) :
    (((0 : SurfaceMask) &&& allowed) == (0 : SurfaceMask)) = true := by
  simp only [beq_iff_eq]; apply uint32_ext_bitvec; ext i hi; simp

/-- Mask inclusion `(m &&& allowed) == m` is reflexive. -/
@[simp]
theorem maskSubset_refl (m : SurfaceMask) :
    ((m &&& m) == m) = true := by
  simp only [beq_iff_eq]; apply uint32_ext_bitvec; ext i hi; simp

/-- Monotonicity under mask inclusion: if `m` is within `allowed₁` and
`allowed₁` is within `allowed₂`, then `m` is within `allowed₂`. -/
theorem maskSubset_mono {m allowed₁ allowed₂ : SurfaceMask}
    (hm : ((m &&& allowed₁) == m) = true)
    (hinc : ((allowed₁ &&& allowed₂) == allowed₁) = true) :
    ((m &&& allowed₂) == m) = true := by
  simp only [beq_iff_eq] at hm hinc ⊢
  calc m &&& allowed₂
      = (m &&& allowed₁) &&& allowed₂ := congrArg (· &&& allowed₂) hm.symm
    _ = m &&& (allowed₁ &&& allowed₂) := surfaceMask_and_assoc m allowed₁ allowed₂
    _ = m &&& allowed₁ := by rw [hinc]
    _ = m := hm

private theorem maskSubset_union_left (a b : SurfaceMask) :
    (((a &&& (a ||| b)) == a)) = true := by
  simp only [beq_iff_eq, surfaceMask_and_or_self_left]

private theorem maskSubset_union_right (a b : SurfaceMask) :
    (((a &&& (b ||| a)) == a)) = true := by
  rw [surfaceMask_or_comm b a]
  exact maskSubset_union_left a b

/-- Mask inclusion `(m &&& allowed) == m` distributes over bitwise union `|||`. -/
@[simp]
theorem maskSubset_or (m₁ m₂ allowed : SurfaceMask) :
    (((m₁ ||| m₂) &&& allowed) == (m₁ ||| m₂)) =
      (((m₁ &&& allowed) == m₁) && ((m₂ &&& allowed) == m₂)) := by
  apply Bool.eq_iff_iff.mpr
  simp only [Bool.and_eq_true]
  constructor
  · intro h
    exact ⟨maskSubset_mono (maskSubset_union_left m₁ m₂) h,
      maskSubset_mono (maskSubset_union_right m₂ m₁) h⟩
  · rintro ⟨h1, h2⟩
    simp only [beq_iff_eq] at h1 h2 ⊢
    rw [surfaceMask_or_and_distrib_right, h1, h2]

/-- Disjointness elimination: if `m` is within `allowed` and `allowed` has no
overlap with `mask`, then `hasMask m mask = false`. -/
theorem hasMask_eq_false_of_maskSubset {m allowed mask : SurfaceMask}
    (hsub : ((m &&& allowed) == m) = true)
    (hdisj : allowed &&& mask = 0) :
    hasMask m mask = false := by
  simp only [beq_iff_eq] at hsub
  simp only [hasMask, bne_eq_false_iff_eq]
  calc m &&& mask
      = (m &&& allowed) &&& mask := congrArg (· &&& mask) hsub.symm
    _ = m &&& (allowed &&& mask) := surfaceMask_and_assoc m allowed mask
    _ = m &&& 0 := by rw [hdisj]
    _ = 0 := surfaceMask_and_zero m

@[simp]
theorem hasMask_bitEventEmit_self : hasMask bitEventEmit bitEventEmit = true := by decide

@[simp]
theorem hasMask_bitInternalCall_self : hasMask bitInternalCall bitInternalCall = true := by decide

@[simp]
theorem hasMask_bitMappingWrite_self : hasMask bitMappingWrite bitMappingWrite = true := by decide

@[simp]
theorem hasMask_bitMulDiv512_self : hasMask bitMulDiv512 bitMulDiv512 = true := by decide

@[simp]
theorem hasMask_bitForEachSetBit_self : hasMask bitForEachSetBit bitForEachSetBit = true := by decide

@[simp]
theorem hasMask_bitInlineYul_self : hasMask bitInlineYul bitInlineYul = true := by decide

/-- `stmtListSurfaceMask` of the empty list is `0`. -/
@[simp]
theorem stmtListSurfaceMask_nil : stmtListSurfaceMask [] = 0 := rfl

/-- `stmtListSurfaceMask` of a `cons` cell is the bitwise union of head and tail masks. -/
@[simp]
theorem stmtListSurfaceMask_cons (s : Stmt) (ss : List Stmt) :
    stmtListSurfaceMask (s :: ss) = (stmtSurfaceMask s ||| stmtListSurfaceMask ss) := rfl

/-- `stmtListSurfaceMask` is a monoid homomorphism from `(List Stmt, ++)` to `(SurfaceMask, |||)`. -/
@[simp]
theorem stmtListSurfaceMask_append (xs ys : List Stmt) :
    stmtListSurfaceMask (xs ++ ys) = (stmtListSurfaceMask xs ||| stmtListSurfaceMask ys) := by
  induction xs with
  | nil => simp [stmtListSurfaceMask_nil]
  | cons x xs ih =>
      simp only [List.cons_append, stmtListSurfaceMask_cons, ih, surfaceMask_or_assoc]

/-! ## Sound Equivalence & Bridge Lemmas to Surface Predicates -/

/-- Node-level event emission head predicate (`Stmt.emit`). -/
def stmtIsEventEmit : Stmt → Bool
  | .emit _ _ => true
  | _ => false

/-- Node-level direct internal helper call predicate (`Stmt.internalCall` / `Stmt.internalCallAssign`). -/
def stmtIsDirectInternalCall : Stmt → Bool
  | .internalCall _ _ | .internalCallAssign _ _ _ => true
  | _ => false

/-- Node-level singleton mapping/struct storage write predicate. -/
def stmtIsMappingWrite : Stmt → Bool
  | .setMapping _ _ _ | .setMappingWord _ _ _ _ | .setMappingPackedWord _ _ _ _ _
  | .setMapping2 _ _ _ _ | .setMapping2Word _ _ _ _ _ | .setMappingUint _ _ _
  | .setMappingChain _ _ _ | .setStructMember _ _ _ _ | .setStructMember2 _ _ _ _ _ => true
  | _ => false

/-- Node-level 512-bit multiply-divide expression predicate (`mulDiv512Down` / `mulDiv512Up`). -/
def exprIsMulDiv512 : Expr → Bool
  | .mulDiv512Down _ _ _ | .mulDiv512Up _ _ _ => true
  | _ => false

/-- Node-level set-bit loop statement predicate (`Stmt.forEachSetBit`). -/
def stmtIsForEachSetBit : Stmt → Bool
  | .forEachSetBit _ _ _ => true
  | _ => false

/-- Node-level inline/unsafe Yul statement predicate (`unsafeBlock` / `unsafeYul`). -/
def stmtIsInlineYul : Stmt → Bool
  | .unsafeBlock _ _ | .unsafeYul _ => true
  | _ => false

/-- Every expression in the core expression fragment `FunctionBody.ExprCompileCore`
touches at most `bitConstructorRaw` (via `calldatasize` / `calldataload`). -/
theorem exprSurfaceMask_subset_of_exprCompileCore
    {e : Expr} (hcore : FunctionBody.ExprCompileCore e) :
    ((exprSurfaceMask e &&& bitConstructorRaw) == exprSurfaceMask e) = true := by
  induction hcore with
  | literal | param | constructorArg | localVar | caller | contractAddress | txOrigin | msgValue
    | blockTimestamp | blockNumber | chainid | blobbasefee | calldatasize | returndataSize =>
      simp [exprSurfaceMask]
  | add _ _ ihL ihR | sub _ _ ihL ihR | mul _ _ ihL ihR | div _ _ ihL ihR | mod _ _ ihL ihR
    | eq _ _ ihL ihR | lt _ _ ihL ihR | gt _ _ ihL ihR | ge _ _ ihL ihR | le _ _ ihL ihR
    | logicalAnd _ _ ihL ihR | logicalOr _ _ ihL ihR | bitAnd _ _ ihL ihR | bitOr _ _ ihL ihR
    | bitXor _ _ ihL ihR | shl _ _ ihL ihR | shr _ _ ihL ihR | min _ _ ihL ihR | max _ _ ihL ihR
    | ceilDiv _ _ ihL ihR | wMulDown _ _ ihL ihR | wDivUp _ _ ihL ihR | slt _ _ ihL ihR
    | sgt _ _ ihL ihR | sdiv _ _ ihL ihR | smod _ _ ihL ihR | sar _ _ ihL ihR | byte _ _ ihL ihR
    | signextend _ _ ihL ihR | keccak256 _ _ ihL ihR =>
      simp [exprSurfaceMask, maskSubset_or, ihL, ihR]
  | logicalNot _ ih | bitNot _ ih | tload _ ih | mload _ ih | extcodesize _ ih
    | returndataOptionalBoolAt _ ih =>
      simpa [exprSurfaceMask] using ih
  | calldataload _ ih =>
      simp [exprSurfaceMask, maskSubset_or, ih]
  | ite _ _ _ ihC ihT ihE | mulDivDown _ _ _ ihC ihT ihE | mulDivUp _ _ _ ihC ihT ihE =>
      simp [exprSurfaceMask, maskSubset_or, ihC, ihT, ihE]
  | builtinExp _ _ ihB ihE =>
      simp [exprSurfaceMask, maskSubset_or, ihB, ihE]

/-- Soundness corollary: any `ExprCompileCore` expression has `hasMask = false`
for every surface mask disjoint from `bitConstructorRaw`. -/
theorem hasMask_exprSurfaceMask_eq_false_of_exprCompileCore
    {e : Expr} {mask : SurfaceMask}
    (hcore : FunctionBody.ExprCompileCore e)
    (hdisj : bitConstructorRaw &&& mask = 0) :
    hasMask (exprSurfaceMask e) mask = false :=
  hasMask_eq_false_of_maskSubset (exprSurfaceMask_subset_of_exprCompileCore hcore) hdisj

/-- Every statement list in `FunctionBody.StmtListCompileCore` touches at most `bitConstructorRaw`. -/
theorem stmtListSurfaceMask_subset_of_stmtListCompileCore
    {scope : List String} {stmts : List Stmt}
    (hcore : FunctionBody.StmtListCompileCore scope stmts) :
    ((stmtListSurfaceMask stmts &&& bitConstructorRaw) == stmtListSurfaceMask stmts) = true := by
  induction hcore with
  | nil => decide
  | letVar hv _ _ ih | assignVar hv _ _ ih | require_ hv _ _ ih | return_ hv _ _ ih =>
      simp [stmtListSurfaceMask, stmtSurfaceMask, maskSubset_or,
        exprSurfaceMask_subset_of_exprCompileCore hv, ih]
  | stop _ ih =>
      simpa [stmtListSurfaceMask, stmtSurfaceMask] using ih
  | mstore ho _ hv _ _ ih | tstore ho _ hv _ _ ih =>
      simp [stmtListSurfaceMask, stmtSurfaceMask, maskSubset_or,
        exprSurfaceMask_subset_of_exprCompileCore ho,
        exprSurfaceMask_subset_of_exprCompileCore hv, ih]

/-- Soundness for event emission: if `bitEventEmit` is absent from `stmtSurfaceMask s`,
then `stmtIsEventEmit s = false`. -/
theorem stmtIsEventEmit_eq_false_of_no_eventEmitMask
    {s : Stmt} (h : hasMask (stmtSurfaceMask s) bitEventEmit = false) :
    stmtIsEventEmit s = false := by
  cases s with
  | emit _ args => simp [stmtSurfaceMask, hasMask_or] at h
  | _ => rfl

/-- Soundness for direct internal-helper calls: if `bitInternalCall` is absent from
`stmtSurfaceMask s`, then `stmtIsDirectInternalCall s = false`. -/
theorem stmtIsDirectInternalCall_eq_false_of_no_internalCallMask
    {s : Stmt} (h : hasMask (stmtSurfaceMask s) bitInternalCall = false) :
    stmtIsDirectInternalCall s = false := by
  cases s with
  | internalCall _ args | internalCallAssign _ _ args =>
      simp [stmtSurfaceMask, hasMask_or] at h
  | _ => rfl

/-- Soundness for mapping writes: if `bitMappingWrite` is absent from `stmtSurfaceMask s`,
then `stmtIsMappingWrite s = false`. -/
theorem stmtIsMappingWrite_eq_false_of_no_mappingWriteMask
    {s : Stmt} (h : hasMask (stmtSurfaceMask s) bitMappingWrite = false) :
    stmtIsMappingWrite s = false := by
  cases s with
  | setMapping _ _ _ | setMappingWord _ _ _ _ | setMappingPackedWord _ _ _ _ _
  | setMapping2 _ _ _ _ | setMapping2Word _ _ _ _ _ | setMappingUint _ _ _
  | setMappingChain _ _ _ | setStructMember _ _ _ _ | setStructMember2 _ _ _ _ _ =>
      simp [stmtSurfaceMask, hasMask_or] at h
  | _ => rfl

/-- Soundness for 512-bit multiply-divide: if `bitMulDiv512` is absent from
`exprSurfaceMask e`, then `exprIsMulDiv512 e = false`. -/
theorem exprIsMulDiv512_eq_false_of_no_mulDiv512Mask
    {e : Expr} (h : hasMask (exprSurfaceMask e) bitMulDiv512 = false) :
    exprIsMulDiv512 e = false := by
  cases e with
  | mulDiv512Down _ _ _ | mulDiv512Up _ _ _ =>
      simp [exprSurfaceMask, hasMask_or] at h
  | _ => rfl

/-- Soundness for set-bit iteration: if `bitForEachSetBit` is absent from
`stmtSurfaceMask s`, then `stmtIsForEachSetBit s = false`. -/
theorem stmtIsForEachSetBit_eq_false_of_no_forEachSetBitMask
    {s : Stmt} (h : hasMask (stmtSurfaceMask s) bitForEachSetBit = false) :
    stmtIsForEachSetBit s = false := by
  cases s with
  | forEachSetBit _ _ _ =>
      simp [stmtSurfaceMask, hasMask_or] at h
  | _ => rfl

/-- Soundness for inline Yul: if `bitInlineYul` is absent from `stmtSurfaceMask s`,
then `stmtIsInlineYul s = false`. -/
theorem stmtIsInlineYul_eq_false_of_no_inlineYulMask
    {s : Stmt} (h : hasMask (stmtSurfaceMask s) bitInlineYul = false) :
    stmtIsInlineYul s = false := by
  cases s with
  | unsafeBlock _ _ | unsafeYul _ =>
      simp [stmtSurfaceMask, hasMask_or] at h
  | _ => rfl

/-! ## Layer 3 `EVMYulLean` Revert Payload & `memoryguard` Coverage Extension (`#2359`) -/

/-- Surface mask bits discharged when `EvmYulLeanRevertAndMemoryGuard` (`#2359`) is active:
covers custom-error / `Panic` revert payloads (`bitCoreGap`) and Yul `memoryguard` (`bitInlineYul`). -/
def layer3RevertGuardMask : SurfaceMask :=
  bitCoreGap ||| bitInlineYul

/-- Extended proof-coverage predicate: when `layer3RevertGuardActive = true`,
capabilities in `layer3RevertGuardMask` (`bitCoreGap ||| bitInlineYul`) are admitted
alongside `allowed` without altering baseline `maskSubset m allowed` when inactive. -/
def compilerProofCoveredWithLayer3RevertGuard
    (layer3RevertGuardActive : Bool) (allowed m : SurfaceMask) : Bool :=
  if layer3RevertGuardActive then
    maskSubset m (allowed ||| layer3RevertGuardMask)
  else
    maskSubset m allowed

/-- **Layer I Meta-Spec (`Layer3RevertGuardCoverageMetaSpec`, `#2359`)**:
Certifies conservative extension of `maskSubset` under `compilerProofCoveredWithLayer3RevertGuard`. -/
structure Layer3RevertGuardCoverageMetaSpec (allowed : SurfaceMask) : Prop where
  /-- When inactive (`false`), coverage is identical to `maskSubset m allowed`. -/
  inactive_eq_base :
    ∀ m, compilerProofCoveredWithLayer3RevertGuard false allowed m = maskSubset m allowed
  /-- Any mask `m` covered by `allowed` remains covered when Layer 3 revert/memoryguard is active. -/
  active_covers_base :
    ∀ m, maskSubset m allowed = true →
      compilerProofCoveredWithLayer3RevertGuard true allowed m = true
  /-- Any mask `m` within `allowed ||| layer3RevertGuardMask` is covered when active. -/
  active_covers_layer3_revert_and_memoryguard :
    ∀ m, maskSubset m (allowed ||| layer3RevertGuardMask) = true →
      compilerProofCoveredWithLayer3RevertGuard true allowed m = true

/-- **Layer I Universal Theorem (`compilerProofCoveredWithLayer3RevertGuard_satisfies_metaSpec`)**:
For every baseline capability mask `allowed`, `compilerProofCoveredWithLayer3RevertGuard`
satisfies `Layer3RevertGuardCoverageMetaSpec allowed`. -/
theorem compilerProofCoveredWithLayer3RevertGuard_satisfies_metaSpec
    (allowed : SurfaceMask) :
    Layer3RevertGuardCoverageMetaSpec allowed where
  inactive_eq_base _ := rfl
  active_covers_base m hm := by
    simp only [compilerProofCoveredWithLayer3RevertGuard, maskSubset] at hm ⊢
    exact maskSubset_mono hm (maskSubset_union_left allowed layer3RevertGuardMask)
  active_covers_layer3_revert_and_memoryguard _ hm := hm

/-- **Layer II Corollary 1 (`compilerProofCoveredWithLayer3RevertGuard_of_maskSubset`)**:
Monotonicity of `compilerProofCoveredWithLayer3RevertGuard` over baseline `maskSubset`. -/
theorem compilerProofCoveredWithLayer3RevertGuard_of_maskSubset
    {allowed m : SurfaceMask} (hm : maskSubset m allowed = true) :
    compilerProofCoveredWithLayer3RevertGuard true allowed m = true :=
  (compilerProofCoveredWithLayer3RevertGuard_satisfies_metaSpec allowed).active_covers_base m hm

/-- **Layer II Corollary 2 (`compilerProofCoveredWithLayer3RevertGuard_panic`)**:
`Stmt.panic` statements are covered under `compilerProofCoveredWithLayer3RevertGuard true allowed`. -/
theorem compilerProofCoveredWithLayer3RevertGuard_panic
    (allowed : SurfaceMask) (code : Verity.Core.PanicCode) :
    compilerProofCoveredWithLayer3RevertGuard true allowed
      (stmtSurfaceMask (.panic code)) = true := by
  simp only [compilerProofCoveredWithLayer3RevertGuard, stmtSurfaceMask, maskSubset]
  exact maskSubset_mono (by decide : ((bitCoreGap &&& layer3RevertGuardMask) == bitCoreGap) = true)
    (maskSubset_union_right layer3RevertGuardMask allowed)

/-- **Layer II Corollary 3 (`compilerProofCoveredWithLayer3RevertGuard_unsafeYul_memoryguard`)**:
`Stmt.unsafeYul` (`memoryguard(0x80)`) is covered under `compilerProofCoveredWithLayer3RevertGuard true allowed`. -/
theorem compilerProofCoveredWithLayer3RevertGuard_unsafeYul_memoryguard
    (allowed : SurfaceMask) (fragment : UnsafeYulFragment) :
    compilerProofCoveredWithLayer3RevertGuard true allowed
      (stmtSurfaceMask (.unsafeYul fragment)) = true := by
  simp only [compilerProofCoveredWithLayer3RevertGuard, stmtSurfaceMask, maskSubset]
  exact maskSubset_mono (by decide : ((bitInlineYul &&& layer3RevertGuardMask) == bitInlineYul) = true)
    (maskSubset_union_right layer3RevertGuardMask allowed)

/-- **Layer II Corollary 4 (`compilerProofCoveredWithLayer3RevertGuard_revertError`)**:
Custom-error `Stmt.revertError errName args` is covered whenever `args` stay within `allowed`. -/
theorem compilerProofCoveredWithLayer3RevertGuard_revertError
    (allowed : SurfaceMask) (errName : String) (args : List Expr)
    (hArgs : maskSubset (exprListSurfaceMask args) allowed = true) :
    compilerProofCoveredWithLayer3RevertGuard true allowed
      (stmtSurfaceMask (.revertError errName args)) = true := by
  simp only [compilerProofCoveredWithLayer3RevertGuard, stmtSurfaceMask, maskSubset, ↓reduceIte] at hArgs ⊢
  rw [maskSubset_or, Bool.and_eq_true]
  exact ⟨maskSubset_mono (by decide : ((bitCoreGap &&& layer3RevertGuardMask) == bitCoreGap) = true)
      (maskSubset_union_right layer3RevertGuardMask allowed),
    maskSubset_mono hArgs (maskSubset_union_left allowed layer3RevertGuardMask)⟩

/-- **Layer III Witness 1**: EIP-6093 `ERC20InsufficientBalance` custom error is covered when active. -/
theorem witness_layer3_revertError_covered :
    compilerProofCoveredWithLayer3RevertGuard true 0
      (stmtSurfaceMask (.revertError "ERC20InsufficientBalance" [.literal 1, .literal 2])) = true := by
  decide

/-- **Layer III Witness 2**: `Panic(0x11)` (`PanicCode.arithmeticOverflow`) is covered when active. -/
theorem witness_layer3_panic_covered :
    compilerProofCoveredWithLayer3RevertGuard true 0
      (stmtSurfaceMask (.panic .arithmeticOverflow)) = true := by
  decide

/-- **Layer III Witness 3**: Yul `memoryguard(0x80)` block is covered when active. -/
theorem witness_layer3_memoryguard_covered :
    compilerProofCoveredWithLayer3RevertGuard true 0
      (stmtSurfaceMask (.unsafeBlock "memoryguard(0x80)" [])) = true := by
  decide

/-- **Layer III Witness 4**: Custom-error revert is rejected at mask `0` when Layer 3 guard is inactive. -/
theorem witness_layer3_inactive_rejects_customError :
    compilerProofCoveredWithLayer3RevertGuard false 0
      (stmtSurfaceMask (.revertError "CustomErr" [])) = false := by
  decide

end Compiler.Proofs.IRGeneration
