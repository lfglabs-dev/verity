import Compiler.Proofs.IRGeneration.SourceSemantics
import Verity.Core.Model.Denote

/-!
# Agreement between the compiler-free denotation and `SourceSemantics` (P4)

`Verity.Core.Model.Denote` mirrors `SourceSemantics` arm-for-arm, routing the
two compiler-engine dependencies (mapping-slot hashing and Keccak over a
memory slice) through a `DenoteOracle`. This file instantiates that oracle
with the real engines (`sourceOracle`) and proves that the two expression
evaluators agree on every expression (and expression list).

The proofs deliberately avoid `simp [Denote.evalExpr, SourceSemantics.evalExpr]`
and functional induction: realizing the derived equations / induction principle
for these ~90-arm matches exceeds the (non-configurable) realization budget,
which is also why `SourceSemantics` carries hand-rolled per-arm `rfl` lemmas.
Instead, every arm is closed definitionally (`rfl`) or by the bind-congruence
helper `bindAgree` plus the structural induction hypotheses.
-/

namespace Compiler.Proofs.IRGeneration

open Compiler.CompilationModel

namespace DenoteAgreement

open Compiler.CompilationModel.Denote

/-- Canonical oracle: the engines `SourceSemantics` uses directly. -/
def sourceOracle : DenoteOracle :=
  { mappingSlot := Compiler.Proofs.abstractMappingSlot
    keccakMemorySlice := SourceSemantics.keccakMemorySlice }

/-- The state conversion is field-for-field (the two structures coincide). -/
def toRuntimeState (s : DenoteState) : SourceSemantics.RuntimeState :=
  { world := s.world, bindings := s.bindings, selector := s.selector }

@[simp] theorem toRuntimeState_world (s : DenoteState) :
    (toRuntimeState s).world = s.world := rfl

@[simp] theorem toRuntimeState_bindings (s : DenoteState) :
    (toRuntimeState s).bindings = s.bindings := rfl

@[simp] theorem toRuntimeState_selector (s : DenoteState) :
    (toRuntimeState s).selector = s.selector := rfl

@[simp] theorem sourceOracle_mappingSlot :
    sourceOracle.mappingSlot = Compiler.Proofs.abstractMappingSlot := rfl

@[simp] theorem sourceOracle_keccakMemorySlice :
    sourceOracle.keccakMemorySlice = SourceSemantics.keccakMemorySlice := rfl

/-- Congruence for `Option.bind`: used to thread induction hypotheses through
the `do`-blocks shared by `Denote.evalExpr` and `SourceSemantics.evalExpr`. -/
theorem bindAgree {α β : Type} {o₁ o₂ : Option α} {f g : α → Option β}
    (h : o₁ = o₂) (hf : ∀ x, f x = g x) : o₁.bind f = o₂.bind g := by
  cases h
  exact congrArg _ (funext hf)

/-! ## Expression-level agreement -/

theorem denote_evalExpr_eq (fields : List Field) (s : DenoteState) :
    ∀ e : Expr,
      Denote.evalExpr sourceOracle fields s e =
        SourceSemantics.evalExpr fields (toRuntimeState s) e
  | .literal _ | .param _ | .constructorArg _ | .storage _ | .storageAddr _
  | .mappingChain .. | .localVar _ | .storageArrayLength _ | .dynamicBytesEq ..
  | .memoryArrayLength _ | .memoryArrayElement .. | .arrayElementDynamicDataOffset ..
  | .arrayElementDynamicMemberLength .. | .arrayElementDynamicMemberDataOffset ..
  | .arrayElementDynamicMemberElement .. | .paramDynamicMemberLength ..
  | .paramDynamicMemberDataOffset .. | .paramDynamicMemberElement ..
  | .paramDynamicStaticComposite .. | .paramDynamicHeadWord ..
  | .arrayLength _ | .arrayElement .. | .arrayElementWord .. | .arrayElementDynamicWord ..
  | .call .. | .staticcall .. | .delegatecall .. | .extcodesize _
  | .returndataOptionalBoolAt _ | .externalCall .. | .internalCall ..
  | .intrinsic .. | .forkIfAtLeast .. | .mulDiv512Down .. | .mulDiv512Up ..
  | .adtConstruct .. | .adtTag .. | .adtField ..
  | .caller | .contractAddress | .txOrigin | .chainid | .msgValue | .selfBalance
  | .blockTimestamp | .blockNumber | .blobbasefee | .calldatasize
  | .returndataSize => rfl
  | .bitNot a | .logicalNot a | .mload a | .tload a | .calldataload a
  | .mapping _ a | .mappingWord _ a _ | .mappingPackedWord _ a _ _
  | .mappingUint _ a | .structMember _ a _ | .storageArrayElement _ a =>
      bindAgree (denote_evalExpr_eq fields s a) fun _ => rfl
  | .add a b | .sub a b | .mul a b | .div a b | .sdiv a b | .mod a b | .smod a b
  | .bitAnd a b | .bitOr a b | .bitXor a b | .shl a b | .shr a b | .sar a b
  | .byte a b | .signextend a b | .eq a b | .ge a b | .gt a b | .sgt a b
  | .lt a b | .slt a b | .le a b | .logicalAnd a b | .logicalOr a b
  | .ceilDiv a b | .wMulDown a b | .wDivUp a b | .min a b | .max a b
  | .keccak256 a b | .mapping2 _ a b | .mapping2Word _ a b _
  | .structMember2 _ a b _ =>
      bindAgree (denote_evalExpr_eq fields s a) fun _ =>
        bindAgree (denote_evalExpr_eq fields s b) fun _ => rfl
  | .mulDivDown a b c | .mulDivUp a b c =>
      bindAgree (denote_evalExpr_eq fields s a) fun _ =>
        bindAgree (denote_evalExpr_eq fields s b) fun _ =>
          bindAgree (denote_evalExpr_eq fields s c) fun _ => rfl
  | .ite c t e =>
      bindAgree (denote_evalExpr_eq fields s c) fun v => by
        by_cases h : (v != 0) = true
        · simpa [h] using denote_evalExpr_eq fields s t
        · simpa [h] using denote_evalExpr_eq fields s e

theorem denote_evalExprList_eq (fields : List Field) (s : DenoteState) :
    ∀ es : List Expr,
      Denote.evalExprList sourceOracle fields s es =
        SourceSemantics.evalExprList fields (toRuntimeState s) es
  | [] => rfl
  | e :: rest =>
      bindAgree (denote_evalExpr_eq fields s e) fun _ =>
        bindAgree (denote_evalExprList_eq fields s rest) fun _ => rfl

end DenoteAgreement

end Compiler.Proofs.IRGeneration
