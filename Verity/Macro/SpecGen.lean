import Verity.Specs.Common
import Verity.Macro.EffectAnalysis
import Verity.Macro.Syntax
import Verity.Proofs.Stdlib.UnfoldSet

namespace Verity.Macro

open Lean

set_option hygiene false

attribute [verity_unfold_simps]
  Verity.msgSender Verity.msgValue Verity.baseFee Verity.gasPrice
  Verity.getStorageAddr Verity.getStorage Verity.setStorage Verity.setStorageAddr
  Verity.getMapping Verity.setMapping Verity.setMapping2 Verity.getMappingUint
  Verity.setMappingUint Verity.getMapping2
  Verity.ContractState.readSlot Verity.ContractState.writeSlot
  Verity.ContractState.readAddrSlot Verity.ContractState.writeAddrSlot
  Verity.ContractState.readMap Verity.ContractState.writeMap
  Verity.ContractState.readMapUint Verity.ContractState.writeMapUint
  Verity.ContractState.readMap2 Verity.ContractState.writeMap2
  Verity.emitEvent List.mapM List.mapM.loop
  Verity.require Verity.pure Verity.bind Bind.bind Pure.pure
  Verity.Contract.run Verity.ContractResult.snd Verity.ContractResult.fst

/-- Evaluate the post-state of a `ContractResult` with EVM rollback `preState`.
Eliminates nested `Contract.run` / `ContractResult.snd` matchers over `if ... then ... else ...`. -/
def evalState {α : Type} (r : Verity.ContractResult α) (preState : Verity.ContractState) :
    Verity.ContractState :=
  match r with
  | .success _ s' => s'
  | .revert _ _ => preState

@[simp high, verity_unfold_simps high] theorem run_snd_eq_evalState
    {α : Type} (c : Verity.Contract α) (s : Verity.ContractState) :
    (c.run s).snd = evalState (c s) s := by
  unfold evalState Verity.Contract.run Verity.ContractResult.snd
  cases c s <;> rfl

@[simp high, verity_unfold_simps high] theorem evalState_success
    {α : Type} (a : α) (s' preState : Verity.ContractState) :
    evalState (Verity.ContractResult.success a s') preState = s' := rfl

@[simp high, verity_unfold_simps high] theorem evalState_revert
    {α : Type} (msg : String) (s' preState : Verity.ContractState) :
    evalState (Verity.ContractResult.revert (α := α) msg s') preState = preState := rfl

@[simp high, verity_unfold_simps high] theorem evalState_ite
    {α : Type} (c : Prop) [Decidable c]
    (x y : Verity.ContractResult α) (preState : Verity.ContractState) :
    evalState (if c then x else y) preState =
      if c then evalState x preState else evalState y preState := by
  by_cases hc : c <;> simp [hc]

@[simp high, verity_unfold_simps high] theorem bind_success_eq
    {α β : Type} (a : Verity.ContractState → α)
    (nextState : Verity.ContractState → Verity.ContractState)
    (f : α → Verity.Contract β) :
    Verity.bind (fun s => Verity.ContractResult.success (a s) (nextState s)) f =
      fun s => f (a s) (nextState s) := rfl

@[simp high, verity_unfold_simps high] theorem bind_revert_eq
    {α β : Type} (msg : Verity.ContractState → String)
    (nextState : Verity.ContractState → Verity.ContractState)
    (f : α → Verity.Contract β) :
    Verity.bind (fun s => Verity.ContractResult.revert (msg s) (nextState s)) f =
      fun s => Verity.ContractResult.revert (msg s) (nextState s) := rfl

@[simp high, verity_unfold_simps high] theorem bind_require_eq
    {α : Type} (cond : Bool) (msg : String) (f : Unit → Verity.Contract α) :
    Verity.bind (Verity.require cond msg) f =
      fun s => if cond = true then f () s else Verity.ContractResult.revert msg s := by
  funext s
  cases cond <;> rfl

@[simp high, verity_unfold_simps high] theorem bind_ite_eq
    {α β : Type} (b : Verity.ContractState → Bool)
    (x y : Verity.ContractState → Verity.ContractResult α)
    (f : α → Verity.Contract β) :
    Verity.bind (fun s' => if b s' = true then x s' else y s') f =
      fun s => if b s = true then Verity.bind x f s else Verity.bind y f s := by
  funext s
  cases hb : b s <;> simp [Verity.bind, hb]

@[simp high, verity_unfold_simps high] theorem snd_ite_contractResult
    {α : Type} (c : Prop) [Decidable c]
    (x y : Verity.ContractResult α) :
    (if c then x else y).snd = if c then x.snd else y.snd := by
  by_cases hc : c <;> simp [hc]

/-- Uniform slot-preservation interface supporting both raw slot indices (`Nat`)
and typed `Verity.StorageSlot` declarations (`Uint256`, `Address`, mappings). -/
class PreservesSlot (α : Type) where
  slotIndex : α → Nat
  preserved : α → Verity.ContractState → Verity.ContractState → Prop

@[simp] instance : PreservesSlot Nat where
  slotIndex n := n
  preserved n s s' := Verity.Specs.sameStorageSlot n s s'

@[simp] instance : PreservesSlot (Verity.StorageSlot Verity.Uint256) where
  slotIndex | ⟨slotIdx⟩ => slotIdx
  preserved | ⟨slotIdx⟩, s, s' => Verity.Specs.sameStorageSlot slotIdx s s'

@[simp] instance : PreservesSlot (Verity.StorageSlot Verity.Address) where
  slotIndex | ⟨slotIdx⟩ => slotIdx
  preserved | ⟨slotIdx⟩, s, s' => Verity.Specs.sameStorageAddrSlot slotIdx s s'

@[simp] instance : PreservesSlot (Verity.StorageSlot (Verity.Address → Verity.Uint256)) where
  slotIndex | ⟨slotIdx⟩ => slotIdx
  preserved | ⟨slotIdx⟩, s, s' => ∀ k, s'.storageMap slotIdx k = s.storageMap slotIdx k

@[simp] instance : PreservesSlot (Verity.StorageSlot (Verity.Uint256 → Verity.Uint256)) where
  slotIndex | ⟨slotIdx⟩ => slotIdx
  preserved | ⟨slotIdx⟩, s, s' => ∀ k, s'.storageMapUint slotIdx k = s.storageMapUint slotIdx k

@[simp] instance : PreservesSlot (Verity.StorageSlot (Verity.Address → Verity.Address → Verity.Uint256)) where
  slotIndex | ⟨slotIdx⟩ => slotIdx
  preserved | ⟨slotIdx⟩, s, s' => ∀ k1 k2, s'.storageMap2 slotIdx k1 k2 = s.storageMap2 slotIdx k1 k2

/-- Single-line frame-obligation discharge tactic combining `verity_unfold_simps`,
bitmask reductions, storage lens simplifications, and kernel `decide`. -/
syntax (name := verityFrameAuto) "verity_frame_auto" : tactic

/-- `verity_frame_auto` with contract-local function and slot simp lemmas. -/
syntax (name := verityFrameAutoWith)
  "verity_frame_auto " "[" Lean.Parser.Tactic.simpLemma,* "]" : tactic

/-- Unified 1-line verification tactic discharging frame obligations (`modifies` / `preserves`),
ANF monadic reductions, and declarative postconditions (`ensures`). -/
syntax (name := verityAuto) "verity_auto" : tactic

/-- `verity_auto` with contract-local function and slot simp lemmas. -/
syntax (name := verityAutoWith)
  "verity_auto " "[" Lean.Parser.Tactic.simpLemma,* "]" : tactic

macro_rules
  | `(tactic| verity_frame_auto) =>
      `(tactic| verity_frame_auto [])
  | `(tactic| verity_frame_auto [ $[$extra:simpLemma],* ]) =>
      `(tactic|
        first
          | decide
          | (intros;
             (try simp +zetaDelta only [$[$extra],*,
               Verity.Macro.PreservesSlot.slotIndex, Verity.Macro.PreservesSlot.preserved,
               Verity.msgSender, Verity.msgValue, Verity.baseFee, Verity.gasPrice,
               Verity.getStorageAddr, Verity.getStorage, Verity.setStorage, Verity.setStorageAddr,
               Verity.getMapping, Verity.setMapping, Verity.setMapping2, Verity.getMappingUint,
               Verity.setMappingUint, Verity.getMapping2,
               Verity.pure, Bind.bind, Pure.pure,
               Verity.Macro.run_snd_eq_evalState, Verity.Macro.evalState_success,
               Verity.Macro.evalState_revert, Verity.Macro.evalState_ite,
               Verity.Macro.bind_success_eq, Verity.Macro.bind_revert_eq,
               Verity.Macro.bind_require_eq, Verity.Macro.bind_ite_eq,
               Verity.Macro.snd_ite_contractResult]);
             (try simp +zetaDelta [verity_unfold_simps, $[$extra],*,
               Verity.Macro.slotsToBitmask, Verity.Macro.bitmaskDisjoint,
               Verity.Macro.slotBitDisjoint, Verity.Macro.slotInBitmask,
               Verity.Macro.PreservesSlot.slotIndex, Verity.Macro.PreservesSlot.preserved,
               Verity.Specs.ToSpecStorageKey.toSpecStorageKey, Verity.Specs.SpecStorageKey.Preserved,
               Verity.Specs.unchangedExcept, Verity.Specs.fnUpdateSpec,
               Verity.Specs.FnSpec.Satisfies,
               Verity.Specs.sameContext, Verity.Specs.sameStorageSlot,
               Verity.Specs.sameStorageAddrSlot, Verity.Specs.sameStorage,
               Verity.Specs.sameStorageAddr, Verity.Specs.sameStorageMap,
               Verity.Specs.sameStorageMapUint, Verity.Specs.sameStorageMap2,
               Verity.Specs.viewPreservesState,
               Verity.ContractState.storage, Verity.ContractState.storageAddr,
               Verity.ContractState.storageMap, Verity.ContractState.storageMapUint,
               Verity.ContractState.storageMap2, Verity.ContractState.transientStorage]);
             repeat' (first
               | decide
               | simp_all +zetaDelta [verity_unfold_simps, $[$extra],*,
                   Verity.Specs.ToSpecStorageKey.toSpecStorageKey, Verity.Specs.SpecStorageKey.Preserved,
                   Verity.Specs.unchangedExcept, Verity.Specs.fnUpdateSpec,
                   Verity.Specs.FnSpec.Satisfies,
                   Verity.Specs.sameContext, Verity.Specs.sameStorageSlot,
                   Verity.Specs.sameStorageAddrSlot, Verity.Specs.sameStorage,
                   Verity.Specs.viewPreservesState]
               | (split <;> try simp_all +zetaDelta [verity_unfold_simps, $[$extra],*,
                   Verity.Specs.ToSpecStorageKey.toSpecStorageKey, Verity.Specs.SpecStorageKey.Preserved,
                   Verity.Specs.unchangedExcept, Verity.Specs.fnUpdateSpec,
                   Verity.Specs.FnSpec.Satisfies,
                   Verity.Specs.sameContext, Verity.Specs.sameStorageSlot,
                   Verity.Specs.sameStorageAddrSlot, Verity.Specs.sameStorage,
                   Verity.Specs.viewPreservesState]))))
  | `(tactic| verity_auto) =>
      `(tactic| verity_auto [])
  | `(tactic| verity_auto [ $[$extra:simpLemma],* ]) =>
      `(tactic|
        first
          | decide
          | (intros;
             (try simp +zetaDelta only [$[$extra],*,
               Verity.Macro.PreservesSlot.slotIndex, Verity.Macro.PreservesSlot.preserved,
               Verity.Specs.ToSpecStorageKey.toSpecStorageKey, Verity.Specs.SpecStorageKey.Preserved,
               Verity.msgSender, Verity.msgValue, Verity.baseFee, Verity.gasPrice,
               Verity.getStorageAddr, Verity.getStorage, Verity.setStorage, Verity.setStorageAddr,
               Verity.getMapping, Verity.setMapping, Verity.setMapping2, Verity.getMappingUint,
               Verity.setMappingUint, Verity.getMapping2,
               Verity.pure, Bind.bind, Pure.pure,
               Verity.Macro.run_snd_eq_evalState, Verity.Macro.evalState_success,
               Verity.Macro.evalState_revert, Verity.Macro.evalState_ite,
               Verity.Macro.bind_success_eq, Verity.Macro.bind_revert_eq,
               Verity.Macro.bind_require_eq, Verity.Macro.bind_ite_eq,
               Verity.Macro.snd_ite_contractResult]);
             (try simp +zetaDelta [verity_unfold_simps, $[$extra],*,
               Verity.Macro.slotsToBitmask, Verity.Macro.bitmaskDisjoint,
               Verity.Macro.slotBitDisjoint, Verity.Macro.slotInBitmask,
               Verity.Macro.PreservesSlot.slotIndex, Verity.Macro.PreservesSlot.preserved,
               Verity.Specs.ToSpecStorageKey.toSpecStorageKey, Verity.Specs.SpecStorageKey.Preserved,
               Verity.Specs.unchangedExcept, Verity.Specs.fnUpdateSpec,
               Verity.Specs.FnSpec.Satisfies,
               Verity.Specs.sameContext, Verity.Specs.sameStorageSlot,
               Verity.Specs.sameStorageAddrSlot, Verity.Specs.sameStorage,
               Verity.Specs.sameStorageAddr, Verity.Specs.sameStorageMap,
               Verity.Specs.sameStorageMapUint, Verity.Specs.sameStorageMap2,
               Verity.Specs.storageUpdateSpec, Verity.Specs.storageAddrUpdateSpec,
               Verity.Specs.storageUnchangedExcept, Verity.Specs.storageAddrUnchangedExcept,
               Verity.Specs.viewPreservesState,
               Verity.ContractState.storage, Verity.ContractState.storageAddr,
               Verity.ContractState.storageMap, Verity.ContractState.storageMapUint,
               Verity.ContractState.storageMap2, Verity.ContractState.transientStorage,
               Verity.ContractResult.getValue?, Verity.ContractResult.isSuccess]);
             repeat' (first
               | decide
               | omega
               | simp_all +zetaDelta [verity_unfold_simps, $[$extra],*,
                   Verity.Specs.ToSpecStorageKey.toSpecStorageKey, Verity.Specs.SpecStorageKey.Preserved,
                   Verity.Specs.unchangedExcept, Verity.Specs.fnUpdateSpec,
                   Verity.Specs.FnSpec.Satisfies,
                   Verity.Specs.sameContext, Verity.Specs.sameStorageSlot,
                   Verity.Specs.sameStorageAddrSlot, Verity.Specs.sameStorage,
                   Verity.Specs.storageUnchangedExcept, Verity.Specs.storageAddrUnchangedExcept,
                   Verity.Specs.viewPreservesState]
               | (split <;> try simp_all +zetaDelta [verity_unfold_simps, $[$extra],*,
                   Verity.Specs.ToSpecStorageKey.toSpecStorageKey, Verity.Specs.SpecStorageKey.Preserved,
                   Verity.Specs.unchangedExcept, Verity.Specs.fnUpdateSpec,
                   Verity.Specs.FnSpec.Satisfies,
                   Verity.Specs.sameContext, Verity.Specs.sameStorageSlot,
                   Verity.Specs.sameStorageAddrSlot, Verity.Specs.sameStorage,
                   Verity.Specs.storageUnchangedExcept, Verity.Specs.storageAddrUnchangedExcept,
                   Verity.Specs.viewPreservesState]))))

/-- Canonical two-state specification for `view` functions (`#2422`, `#1994`, `#1895`):
asserts `Verity.Specs.viewPreservesState s s'` together with an optional
postcondition `extra s s'`. -/
def viewFrameSpec
    (extra : Verity.ContractState → Verity.ContractState → Prop := fun _ _ => True)
    (s s' : Verity.ContractState) : Prop :=
  Verity.Specs.viewPreservesState s s' ∧ extra s s'

@[simp]
theorem viewFrameSpec_rfl (s : Verity.ContractState) :
    viewFrameSpec (fun _ _ => True) s s :=
  ⟨Verity.Specs.viewPreservesState_rfl s, trivial⟩

/-- Specialization of `view_frame_of_writesStorage_false` to `Verity.ContractState`
when a `Contract α` computation preserves state (`(m.run s).snd = s`). -/
theorem view_frame_preserves_state_of_run_snd_eq
    {α : Type} (m : Verity.Contract α) (s : Verity.ContractState)
    (heq : (m.run s).snd = s) :
    Verity.Specs.viewPreservesState s (m.run s).snd := by
  rw [heq]
  exact Verity.Specs.viewPreservesState_rfl s

/-- Discharge `viewFrameSpec` whenever a `Contract α` computation preserves state
(`(m.run s).snd = s`), regardless of whether `m` succeeds or reverts (`#2422`). -/
theorem viewFrameSpec_of_run_snd_eq
    {α : Type} (m : Verity.Contract α) (s : Verity.ContractState)
    (extra : Verity.ContractState → Verity.ContractState → Prop)
    (heq : (m.run s).snd = s)
    (hextra : extra s s) :
    viewFrameSpec extra s (m.run s).snd := by
  rw [heq]
  exact ⟨Verity.Specs.viewPreservesState_rfl s, hextra⟩

/-- Static `MacroEffectSummary` check certifying that `fn` has no persistent or
transient writes and no mutable external interactions (`#2422`). -/
def hasViewEffectFrame
    (functions : List Compiler.CompilationModel.FunctionSpec)
    (fn : Compiler.CompilationModel.FunctionSpec) : Bool :=
  let eff := functionEffectSummary functions fn
  !eff.writesStorage && !eff.writesTransient && !eff.hasExternalInteraction

syntax (name := genSpecViewCmd)
  "#gen_spec_view " ident : command

syntax (name := genSpecViewCmdExtra)
  "#gen_spec_view " ident " (" term ")" : command

syntax (name := genSpecViewCmdFor)
  "#gen_spec_view " ident " for " "(" ident " : " term ")" : command

syntax (name := genSpecViewCmdForExtra)
  "#gen_spec_view " ident " for " "(" ident " : " term ")" " (" term ")" : command

syntax (name := genSpecViewCmdFor2)
  "#gen_spec_view " ident " for2 " "(" ident " : " term ")" " (" ident " : " term ")" : command

syntax (name := genSpecViewCmdFor2Extra)
  "#gen_spec_view " ident " for2 " "(" ident " : " term ")" " (" ident " : " term ")"
    " (" term ")" : command

syntax (name := genSpecCmd)
  "#gen_spec " ident " (" term ", " term ", " term ")" : command

syntax (name := genSpecCmdExtra)
  "#gen_spec " ident " (" term ", " term ", " term ", " term ")" : command

syntax (name := genSpecCmdFor)
  "#gen_spec " ident " for " "(" ident " : " term ")" " (" term ", " term ", " term ")" : command

syntax (name := genSpecCmdForExtra)
  "#gen_spec " ident " for " "(" ident " : " term ")" " (" term ", " term ", " term ", " term ")" : command

syntax (name := genSpecCmdFor2)
  "#gen_spec " ident " for2 " "(" ident " : " term ")" " (" ident " : " term ")"
    " (" term ", " term ", " term ")" : command

syntax (name := genSpecCmdFor2Extra)
  "#gen_spec " ident " for2 " "(" ident " : " term ")" " (" ident " : " term ")"
    " (" term ", " term ", " term ", " term ")" : command

syntax (name := genSpecAddrCmd)
  "#gen_spec_addr " ident " (" term ", " term ", " term ")" : command

syntax (name := genSpecAddrCmdExtra)
  "#gen_spec_addr " ident " (" term ", " term ", " term ", " term ")" : command

syntax (name := genSpecAddrCmdFor)
  "#gen_spec_addr " ident " for " "(" ident " : " term ")" " (" term ", " term ", " term ")" : command

syntax (name := genSpecAddrCmdForExtra)
  "#gen_spec_addr " ident " for " "(" ident " : " term ")" " (" term ", " term ", " term ", " term ")" : command

syntax (name := genSpecAddrCmdFor2)
  "#gen_spec_addr " ident " for2 " "(" ident " : " term ")" " (" ident " : " term ")"
    " (" term ", " term ", " term ")" : command

syntax (name := genSpecAddrCmdFor2Extra)
  "#gen_spec_addr " ident " for2 " "(" ident " : " term ")" " (" ident " : " term ")"
    " (" term ", " term ", " term ", " term ")" : command

syntax (name := genSpecAddrStorageCmd)
  "#gen_spec_addr_storage " ident
    " (" term ", " term ", " term ", " term ", " term ")" : command

syntax (name := genSpecAddrStorageCmdExtra)
  "#gen_spec_addr_storage " ident
    " (" term ", " term ", " term ", " term ", " term ", " term ")" : command

syntax (name := genSpecAddrStorageCmdFor)
  "#gen_spec_addr_storage " ident " for " "(" ident " : " term ")"
    " (" term ", " term ", " term ", " term ", " term ")" : command

syntax (name := genSpecAddrStorageCmdForExtra)
  "#gen_spec_addr_storage " ident " for " "(" ident " : " term ")"
    " (" term ", " term ", " term ", " term ", " term ", " term ")" : command

syntax (name := genSpecAddrStorageCmdFor2)
  "#gen_spec_addr_storage " ident " for2 " "(" ident " : " term ")" " (" ident " : " term ")"
    " (" term ", " term ", " term ", " term ", " term ")" : command

syntax (name := genSpecAddrStorageCmdFor2Extra)
  "#gen_spec_addr_storage " ident " for2 " "(" ident " : " term ")" " (" ident " : " term ")"
    " (" term ", " term ", " term ", " term ", " term ", " term ")" : command

syntax (name := genSpecAddrStorage2Cmd)
  "#gen_spec_addr_storage2 " ident
    " (" term ", " term ", " term ", " term ", " term ", " term ", " term ")" : command

syntax (name := genSpecAddrStorage2CmdExtra)
  "#gen_spec_addr_storage2 " ident
    " (" term ", " term ", " term ", " term ", " term ", " term ", " term ", " term ")" : command

syntax (name := genSpecAddrStorage2CmdFor)
  "#gen_spec_addr_storage2 " ident " for " "(" ident " : " term ")"
    " (" term ", " term ", " term ", " term ", " term ", " term ", " term ")" : command

syntax (name := genSpecAddrStorage2CmdForExtra)
  "#gen_spec_addr_storage2 " ident " for " "(" ident " : " term ")"
    " (" term ", " term ", " term ", " term ", " term ", " term ", " term ", " term ")" : command

syntax (name := genSpecAddrStorage2CmdFor2)
  "#gen_spec_addr_storage2 " ident " for2 "
    "(" ident " : " term ")" " (" ident " : " term ")"
    " (" term ", " term ", " term ", " term ", " term ", " term ", " term ")" : command

syntax (name := genSpecAddrStorage2CmdFor2Extra)
  "#gen_spec_addr_storage2 " ident " for2 "
    "(" ident " : " term ")" " (" ident " : " term ")"
    " (" term ", " term ", " term ", " term ", " term ", " term ", " term ", " term ")" : command

syntax (name := genSpecMapCmd)
  "#gen_spec_map " ident
    " (" term ", " term ", " term ", " term ")" : command

syntax (name := genSpecMapCmdExtra)
  "#gen_spec_map " ident
    " (" term ", " term ", " term ", " term ", " term ")" : command

syntax (name := genSpecMapCmdFor)
  "#gen_spec_map " ident " for " "(" ident " : " term ")"
    " (" term ", " term ", " term ", " term ")" : command

syntax (name := genSpecMapCmdForExtra)
  "#gen_spec_map " ident " for " "(" ident " : " term ")"
    " (" term ", " term ", " term ", " term ", " term ")" : command

syntax (name := genSpecMapCmdFor2)
  "#gen_spec_map " ident " for2 " "(" ident " : " term ")" " (" ident " : " term ")"
    " (" term ", " term ", " term ", " term ")" : command

syntax (name := genSpecMapCmdFor2Extra)
  "#gen_spec_map " ident " for2 " "(" ident " : " term ")" " (" ident " : " term ")"
    " (" term ", " term ", " term ", " term ", " term ")" : command

syntax (name := genSpecMapStorageCmd)
  "#gen_spec_map_storage " ident
    " (" term ", " term ", " term ", " term ", " term ", " term ")" : command

syntax (name := genSpecMapStorageCmdExtra)
  "#gen_spec_map_storage " ident
    " (" term ", " term ", " term ", " term ", " term ", " term ", " term ")" : command

syntax (name := genSpecMapStorageCmdFor)
  "#gen_spec_map_storage " ident " for " "(" ident " : " term ")"
    " (" term ", " term ", " term ", " term ", " term ", " term ")" : command

syntax (name := genSpecMapStorageCmdForExtra)
  "#gen_spec_map_storage " ident " for " "(" ident " : " term ")"
    " (" term ", " term ", " term ", " term ", " term ", " term ", " term ")" : command

syntax (name := genSpecMapStorageCmdFor2)
  "#gen_spec_map_storage " ident " for "
    "(" ident " : " term ")" " (" ident " : " term ")"
    " (" term ", " term ", " term ", " term ", " term ", " term ")" : command

syntax (name := genSpecMapStorageCmdFor2Alt)
  "#gen_spec_map_storage " ident " for2 "
    "(" ident " : " term ")" " (" ident " : " term ")"
    " (" term ", " term ", " term ", " term ", " term ", " term ")" : command

syntax (name := genSpecMapStorageCmdFor2Extra)
  "#gen_spec_map_storage " ident " for2 "
    "(" ident " : " term ")" " (" ident " : " term ")"
    " (" term ", " term ", " term ", " term ", " term ", " term ", " term ")" : command

syntax (name := genSpecMap2Cmd)
  "#gen_spec_map2 " ident
    " (" term ", " term ", " term ", " term ", " term ")" : command

syntax (name := genSpecMap2CmdExtra)
  "#gen_spec_map2 " ident
    " (" term ", " term ", " term ", " term ", " term ", " term ")" : command

syntax (name := genSpecMap2CmdFor)
  "#gen_spec_map2 " ident " for " "(" ident " : " term ")"
    " (" term ", " term ", " term ", " term ", " term ")" : command

syntax (name := genSpecMap2CmdForExtra)
  "#gen_spec_map2 " ident " for " "(" ident " : " term ")"
    " (" term ", " term ", " term ", " term ", " term ", " term ")" : command

syntax (name := genSpecMap2CmdFor2)
  "#gen_spec_map2 " ident " for2 " "(" ident " : " term ")" " (" ident " : " term ")"
    " (" term ", " term ", " term ", " term ", " term ")" : command

syntax (name := genSpecMap2CmdFor2Extra)
  "#gen_spec_map2 " ident " for2 " "(" ident " : " term ")" " (" ident " : " term ")"
    " (" term ", " term ", " term ", " term ", " term ", " term ")" : command

syntax (name := genSpecMap2CmdFor3)
  "#gen_spec_map2 " ident " for3 "
    "(" ident " : " term ")" " (" ident " : " term ")" " (" ident " : " term ")"
    " (" term ", " term ", " term ", " term ", " term ")" : command

syntax (name := genSpecMap2CmdFor3Extra)
  "#gen_spec_map2 " ident " for3 "
    "(" ident " : " term ")" " (" ident " : " term ")" " (" ident " : " term ")"
    " (" term ", " term ", " term ", " term ", " term ", " term ")" : command

syntax (name := genSpecTransferCmdFor3)
  "#gen_spec_transfer " ident " for3 "
    "(" ident " : " term ")" " (" ident " : " term ")" " (" ident " : " term ")"
    " (" term ", " term ")" : command

syntax (name := genSpecTransferFromCmdFor4)
  "#gen_spec_transfer_from " ident " for4 "
    "(" ident " : " term ")" " (" ident " : " term ")" " (" ident " : " term ")" " (" ident " : " term ")"
    " (" term ", " term ", " term ")" : command

macro_rules
  | `(#gen_spec $name:ident ($slotTerm:term, $value:term, $frame:term)) =>
      `(def $name (s s' : Verity.ContractState) : Prop :=
          Verity.Specs.storageUpdateSpec $slotTerm $value $frame s s')
  | `(#gen_spec $name:ident ($slotTerm:term, $value:term, $frame:term, $extra:term)) =>
      `(def $name (s s' : Verity.ContractState) : Prop :=
          Verity.Specs.storageUpdateSpec $slotTerm $value
            (fun s s' => ($frame) s s' ∧ ($extra) s s') s s')
  | `(#gen_spec_addr $name:ident ($slotTerm:term, $value:term, $frame:term)) =>
      `(def $name (s s' : Verity.ContractState) : Prop :=
          Verity.Specs.storageAddrUpdateSpec $slotTerm $value $frame s s')
  | `(#gen_spec_addr $name:ident ($slotTerm:term, $value:term, $frame:term, $extra:term)) =>
      `(def $name (s s' : Verity.ContractState) : Prop :=
          Verity.Specs.storageAddrUpdateSpec $slotTerm $value
            (fun s s' => ($frame) s s' ∧ ($extra) s s') s s')
  | `(#gen_spec $name:ident for ($arg:ident : $argTy:term) ($slotTerm:term, $value:term, $frame:term)) =>
      `(def $name ($arg : $argTy) (s s' : Verity.ContractState) : Prop :=
          Verity.Specs.storageUpdateSpec $slotTerm $value $frame s s')
  | `(#gen_spec $name:ident for ($arg:ident : $argTy:term) ($slotTerm:term, $value:term, $frame:term, $extra:term)) =>
      `(def $name ($arg : $argTy) (s s' : Verity.ContractState) : Prop :=
          Verity.Specs.storageUpdateSpec $slotTerm $value
            (fun s s' => ($frame) s s' ∧ ($extra) s s') s s')
  | `(#gen_spec $name:ident for2 ($arg1:ident : $argTy1:term) ($arg2:ident : $argTy2:term)
      ($slotTerm:term, $value:term, $frame:term)) =>
      `(def $name ($arg1 : $argTy1) ($arg2 : $argTy2) (s s' : Verity.ContractState) : Prop :=
          Verity.Specs.storageUpdateSpec $slotTerm $value $frame s s')
  | `(#gen_spec $name:ident for2 ($arg1:ident : $argTy1:term) ($arg2:ident : $argTy2:term)
      ($slotTerm:term, $value:term, $frame:term, $extra:term)) =>
      `(def $name ($arg1 : $argTy1) ($arg2 : $argTy2) (s s' : Verity.ContractState) : Prop :=
          Verity.Specs.storageUpdateSpec $slotTerm $value
            (fun s s' => ($frame) s s' ∧ ($extra) s s') s s')
  | `(#gen_spec_addr $name:ident for ($arg:ident : $argTy:term) ($slotTerm:term, $value:term, $frame:term)) =>
      `(def $name ($arg : $argTy) (s s' : Verity.ContractState) : Prop :=
          Verity.Specs.storageAddrUpdateSpec $slotTerm $value $frame s s')
  | `(#gen_spec_addr $name:ident for ($arg:ident : $argTy:term) ($slotTerm:term, $value:term, $frame:term, $extra:term)) =>
      `(def $name ($arg : $argTy) (s s' : Verity.ContractState) : Prop :=
          Verity.Specs.storageAddrUpdateSpec $slotTerm $value
            (fun s s' => ($frame) s s' ∧ ($extra) s s') s s')
  | `(#gen_spec_addr $name:ident for2 ($arg1:ident : $argTy1:term) ($arg2:ident : $argTy2:term)
      ($slotTerm:term, $value:term, $frame:term)) =>
      `(def $name ($arg1 : $argTy1) ($arg2 : $argTy2) (s s' : Verity.ContractState) : Prop :=
          Verity.Specs.storageAddrUpdateSpec $slotTerm $value $frame s s')
  | `(#gen_spec_addr $name:ident for2 ($arg1:ident : $argTy1:term) ($arg2:ident : $argTy2:term)
      ($slotTerm:term, $value:term, $frame:term, $extra:term)) =>
      `(def $name ($arg1 : $argTy1) ($arg2 : $argTy2) (s s' : Verity.ContractState) : Prop :=
          Verity.Specs.storageAddrUpdateSpec $slotTerm $value
            (fun s s' => ($frame) s s' ∧ ($extra) s s') s s')
  | `(#gen_spec_addr_storage $name:ident
      ($addrSlot:term, $storageSlot:term, $addrValue:term, $storageValue:term, $frame:term)) =>
      `(def $name (s s' : Verity.ContractState) : Prop :=
          Verity.Specs.storageAddrStorageUpdateSpec
            $addrSlot $storageSlot $addrValue $storageValue $frame s s')
  | `(#gen_spec_addr_storage $name:ident
      ($addrSlot:term, $storageSlot:term, $addrValue:term, $storageValue:term, $frame:term, $extra:term)) =>
      `(def $name (s s' : Verity.ContractState) : Prop :=
          Verity.Specs.storageAddrStorageUpdateSpec
            $addrSlot $storageSlot $addrValue $storageValue
            (fun s s' => ($frame) s s' ∧ ($extra) s s') s s')
  | `(#gen_spec_addr_storage $name:ident for ($arg:ident : $argTy:term)
      ($addrSlot:term, $storageSlot:term, $addrValue:term, $storageValue:term, $frame:term)) =>
      `(def $name ($arg : $argTy) (s s' : Verity.ContractState) : Prop :=
          Verity.Specs.storageAddrStorageUpdateSpec
            $addrSlot $storageSlot $addrValue $storageValue $frame s s')
  | `(#gen_spec_addr_storage $name:ident for ($arg:ident : $argTy:term)
      ($addrSlot:term, $storageSlot:term, $addrValue:term, $storageValue:term, $frame:term, $extra:term)) =>
      `(def $name ($arg : $argTy) (s s' : Verity.ContractState) : Prop :=
          Verity.Specs.storageAddrStorageUpdateSpec
            $addrSlot $storageSlot $addrValue $storageValue
            (fun s s' => ($frame) s s' ∧ ($extra) s s') s s')
  | `(#gen_spec_addr_storage $name:ident for2 ($arg1:ident : $argTy1:term) ($arg2:ident : $argTy2:term)
      ($addrSlot:term, $storageSlot:term, $addrValue:term, $storageValue:term, $frame:term)) =>
      `(def $name ($arg1 : $argTy1) ($arg2 : $argTy2) (s s' : Verity.ContractState) : Prop :=
          Verity.Specs.storageAddrStorageUpdateSpec
            $addrSlot $storageSlot $addrValue $storageValue $frame s s')
  | `(#gen_spec_addr_storage $name:ident for2 ($arg1:ident : $argTy1:term) ($arg2:ident : $argTy2:term)
      ($addrSlot:term, $storageSlot:term, $addrValue:term, $storageValue:term, $frame:term, $extra:term)) =>
      `(def $name ($arg1 : $argTy1) ($arg2 : $argTy2) (s s' : Verity.ContractState) : Prop :=
          Verity.Specs.storageAddrStorageUpdateSpec
            $addrSlot $storageSlot $addrValue $storageValue
            (fun s s' => ($frame) s s' ∧ ($extra) s s') s s')
  | `(#gen_spec_addr_storage2 $name:ident
      ($addrSlot:term, $storageSlot1:term, $storageSlot2:term,
       $addrValue:term, $storageValue1:term, $storageValue2:term, $frame:term)) =>
      `(def $name (s s' : Verity.ContractState) : Prop :=
          Verity.Specs.storageAddrStorage2UpdateSpec
            $addrSlot $storageSlot1 $storageSlot2
            $addrValue $storageValue1 $storageValue2 $frame s s')
  | `(#gen_spec_addr_storage2 $name:ident
      ($addrSlot:term, $storageSlot1:term, $storageSlot2:term,
       $addrValue:term, $storageValue1:term, $storageValue2:term, $frame:term, $extra:term)) =>
      `(def $name (s s' : Verity.ContractState) : Prop :=
          Verity.Specs.storageAddrStorage2UpdateSpec
            $addrSlot $storageSlot1 $storageSlot2
            $addrValue $storageValue1 $storageValue2
            (fun s s' => ($frame) s s' ∧ ($extra) s s') s s')
  | `(#gen_spec_addr_storage2 $name:ident for ($arg:ident : $argTy:term)
      ($addrSlot:term, $storageSlot1:term, $storageSlot2:term,
       $addrValue:term, $storageValue1:term, $storageValue2:term, $frame:term)) =>
      `(def $name ($arg : $argTy) (s s' : Verity.ContractState) : Prop :=
          Verity.Specs.storageAddrStorage2UpdateSpec
            $addrSlot $storageSlot1 $storageSlot2
            $addrValue $storageValue1 $storageValue2 $frame s s')
  | `(#gen_spec_addr_storage2 $name:ident for ($arg:ident : $argTy:term)
      ($addrSlot:term, $storageSlot1:term, $storageSlot2:term,
       $addrValue:term, $storageValue1:term, $storageValue2:term, $frame:term, $extra:term)) =>
      `(def $name ($arg : $argTy) (s s' : Verity.ContractState) : Prop :=
          Verity.Specs.storageAddrStorage2UpdateSpec
            $addrSlot $storageSlot1 $storageSlot2
            $addrValue $storageValue1 $storageValue2
            (fun s s' => ($frame) s s' ∧ ($extra) s s') s s')
  | `(#gen_spec_addr_storage2 $name:ident for2
      ($arg1:ident : $argTy1:term) ($arg2:ident : $argTy2:term)
      ($addrSlot:term, $storageSlot1:term, $storageSlot2:term,
       $addrValue:term, $storageValue1:term, $storageValue2:term, $frame:term)) =>
      `(def $name ($arg1 : $argTy1) ($arg2 : $argTy2) (s s' : Verity.ContractState) : Prop :=
          Verity.Specs.storageAddrStorage2UpdateSpec
            $addrSlot $storageSlot1 $storageSlot2
            $addrValue $storageValue1 $storageValue2 $frame s s')
  | `(#gen_spec_addr_storage2 $name:ident for2
      ($arg1:ident : $argTy1:term) ($arg2:ident : $argTy2:term)
      ($addrSlot:term, $storageSlot1:term, $storageSlot2:term,
       $addrValue:term, $storageValue1:term, $storageValue2:term, $frame:term, $extra:term)) =>
      `(def $name ($arg1 : $argTy1) ($arg2 : $argTy2) (s s' : Verity.ContractState) : Prop :=
          Verity.Specs.storageAddrStorage2UpdateSpec
            $addrSlot $storageSlot1 $storageSlot2
            $addrValue $storageValue1 $storageValue2
            (fun s s' => ($frame) s s' ∧ ($extra) s s') s s')
  | `(#gen_spec_map $name:ident
      ($slotTerm:term, $key:term, $value:term, $frame:term)) =>
      `(def $name (s s' : Verity.ContractState) : Prop :=
          Verity.Specs.storageMapUpdateSpec
            $slotTerm $key $value $frame s s')
  | `(#gen_spec_map $name:ident
      ($slotTerm:term, $key:term, $value:term, $frame:term, $extra:term)) =>
      `(def $name (s s' : Verity.ContractState) : Prop :=
          Verity.Specs.storageMapUpdateSpec
            $slotTerm $key $value
            (fun s s' => ($frame) s s' ∧ ($extra) s s') s s')
  | `(#gen_spec_map $name:ident for ($arg:ident : $argTy:term)
      ($mapSlot:term, $key:term, $value:term, $frame:term)) =>
      `(def $name ($arg : $argTy) (s s' : Verity.ContractState) : Prop :=
          Verity.Specs.storageMapUpdateSpec
            $mapSlot $key $value $frame s s')
  | `(#gen_spec_map $name:ident for ($arg:ident : $argTy:term)
      ($slotTerm:term, $key:term, $value:term, $frame:term, $extra:term)) =>
      `(def $name ($arg : $argTy) (s s' : Verity.ContractState) : Prop :=
          Verity.Specs.storageMapUpdateSpec
            $slotTerm $key $value
            (fun s s' => ($frame) s s' ∧ ($extra) s s') s s')
  | `(#gen_spec_map $name:ident for2 ($arg1:ident : $argTy1:term) ($arg2:ident : $argTy2:term)
      ($slotTerm:term, $key:term, $value:term, $frame:term)) =>
      `(def $name ($arg1 : $argTy1) ($arg2 : $argTy2) (s s' : Verity.ContractState) : Prop :=
          Verity.Specs.storageMapUpdateSpec
            $slotTerm $key $value $frame s s')
  | `(#gen_spec_map $name:ident for2 ($arg1:ident : $argTy1:term) ($arg2:ident : $argTy2:term)
      ($slotTerm:term, $key:term, $value:term, $frame:term, $extra:term)) =>
      `(def $name ($arg1 : $argTy1) ($arg2 : $argTy2) (s s' : Verity.ContractState) : Prop :=
          Verity.Specs.storageMapUpdateSpec
            $slotTerm $key $value
            (fun s s' => ($frame) s s' ∧ ($extra) s s') s s')
  | `(#gen_spec_map_storage $name:ident
      ($mapSlot:term, $key:term, $mapValue:term,
       $storageSlot:term, $storageValue:term, $frame:term)) =>
      `(def $name (s s' : Verity.ContractState) : Prop :=
          Verity.Specs.storageMapAndStorageUpdateSpec
            $mapSlot $key $mapValue
            $storageSlot $storageValue $frame s s')
  | `(#gen_spec_map_storage $name:ident
      ($mapSlot:term, $key:term, $mapValue:term,
       $storageSlot:term, $storageValue:term, $frame:term, $extra:term)) =>
      `(def $name (s s' : Verity.ContractState) : Prop :=
          Verity.Specs.storageMapAndStorageUpdateSpec
            $mapSlot $key $mapValue
            $storageSlot $storageValue
            (fun s s' => ($frame) s s' ∧ ($extra) s s') s s')
  | `(#gen_spec_map_storage $name:ident for ($arg:ident : $argTy:term)
      ($mapSlot:term, $key:term, $mapValue:term,
       $storageSlot:term, $storageValue:term, $frame:term)) =>
      `(def $name ($arg : $argTy) (s s' : Verity.ContractState) : Prop :=
          Verity.Specs.storageMapAndStorageUpdateSpec
            $mapSlot $key $mapValue
            $storageSlot $storageValue $frame s s')
  | `(#gen_spec_map_storage $name:ident for ($arg:ident : $argTy:term)
      ($mapSlot:term, $key:term, $mapValue:term,
       $storageSlot:term, $storageValue:term, $frame:term, $extra:term)) =>
      `(def $name ($arg : $argTy) (s s' : Verity.ContractState) : Prop :=
          Verity.Specs.storageMapAndStorageUpdateSpec
            $mapSlot $key $mapValue
            $storageSlot $storageValue
            (fun s s' => ($frame) s s' ∧ ($extra) s s') s s')
  | `(#gen_spec_map_storage $name:ident for
      ($arg1:ident : $argTy1:term) ($arg2:ident : $argTy2:term)
      ($mapSlot:term, $key:term, $mapValue:term, $storageSlot:term, $storageValue:term, $frame:term)) =>
      `(def $name ($arg1 : $argTy1) ($arg2 : $argTy2) (s s' : Verity.ContractState) : Prop :=
          Verity.Specs.storageMapAndStorageUpdateSpec
            $mapSlot $key $mapValue
            $storageSlot $storageValue
            $frame s s')
  | `(#gen_spec_map_storage $name:ident for2
      ($arg1:ident : $argTy1:term) ($arg2:ident : $argTy2:term)
      ($mapSlot:term, $key:term, $mapValue:term, $storageSlot:term, $storageValue:term, $frame:term)) =>
      `(def $name ($arg1 : $argTy1) ($arg2 : $argTy2) (s s' : Verity.ContractState) : Prop :=
          Verity.Specs.storageMapAndStorageUpdateSpec
            $mapSlot $key $mapValue
            $storageSlot $storageValue $frame s s')
  | `(#gen_spec_map_storage $name:ident for2
      ($arg1:ident : $argTy1:term) ($arg2:ident : $argTy2:term)
      ($mapSlot:term, $key:term, $mapValue:term, $storageSlot:term, $storageValue:term, $frame:term, $extra:term)) =>
      `(def $name ($arg1 : $argTy1) ($arg2 : $argTy2) (s s' : Verity.ContractState) : Prop :=
          Verity.Specs.storageMapAndStorageUpdateSpec
            $mapSlot $key $mapValue
            $storageSlot $storageValue
            (fun s s' => ($frame) s s' ∧ ($extra) s s') s s')
  | `(#gen_spec_map2 $name:ident
      ($slotTerm:term, $key1:term, $key2:term, $value:term, $frame:term)) =>
      `(def $name (s s' : Verity.ContractState) : Prop :=
          Verity.Specs.storageMap2UpdateSpec
            $slotTerm $key1 $key2 $value $frame s s')
  | `(#gen_spec_map2 $name:ident
      ($slotTerm:term, $key1:term, $key2:term, $value:term, $frame:term, $extra:term)) =>
      `(def $name (s s' : Verity.ContractState) : Prop :=
          Verity.Specs.storageMap2UpdateSpec
            $slotTerm $key1 $key2 $value
            (fun s s' => ($frame) s s' ∧ ($extra) s s') s s')
  | `(#gen_spec_map2 $name:ident for ($arg:ident : $argTy:term)
      ($slotTerm:term, $key1:term, $key2:term, $value:term, $frame:term)) =>
      `(def $name ($arg : $argTy) (s s' : Verity.ContractState) : Prop :=
          Verity.Specs.storageMap2UpdateSpec
            $slotTerm $key1 $key2 $value $frame s s')
  | `(#gen_spec_map2 $name:ident for ($arg:ident : $argTy:term)
      ($slotTerm:term, $key1:term, $key2:term, $value:term, $frame:term, $extra:term)) =>
      `(def $name ($arg : $argTy) (s s' : Verity.ContractState) : Prop :=
          Verity.Specs.storageMap2UpdateSpec
            $slotTerm $key1 $key2 $value
            (fun s s' => ($frame) s s' ∧ ($extra) s s') s s')
  | `(#gen_spec_map2 $name:ident for2 ($arg1:ident : $argTy1:term) ($arg2:ident : $argTy2:term)
      ($slotTerm:term, $key1:term, $key2:term, $value:term, $frame:term)) =>
      `(def $name ($arg1 : $argTy1) ($arg2 : $argTy2) (s s' : Verity.ContractState) : Prop :=
          Verity.Specs.storageMap2UpdateSpec
            $slotTerm $key1 $key2 $value $frame s s')
  | `(#gen_spec_map2 $name:ident for2 ($arg1:ident : $argTy1:term) ($arg2:ident : $argTy2:term)
      ($slotTerm:term, $key1:term, $key2:term, $value:term, $frame:term, $extra:term)) =>
      `(def $name ($arg1 : $argTy1) ($arg2 : $argTy2) (s s' : Verity.ContractState) : Prop :=
          Verity.Specs.storageMap2UpdateSpec
            $slotTerm $key1 $key2 $value
            (fun s s' => ($frame) s s' ∧ ($extra) s s') s s')
  | `(#gen_spec_map2 $name:ident for3
      ($arg1:ident : $argTy1:term) ($arg2:ident : $argTy2:term) ($arg3:ident : $argTy3:term)
      ($slotTerm:term, $key1:term, $key2:term, $value:term, $frame:term)) =>
      `(def $name ($arg1 : $argTy1) ($arg2 : $argTy2) ($arg3 : $argTy3) (s s' : Verity.ContractState) : Prop :=
          Verity.Specs.storageMap2UpdateSpec
            $slotTerm $key1 $key2 $value $frame s s')
  | `(#gen_spec_map2 $name:ident for3
      ($arg1:ident : $argTy1:term) ($arg2:ident : $argTy2:term) ($arg3:ident : $argTy3:term)
      ($slotTerm:term, $key1:term, $key2:term, $value:term, $frame:term, $extra:term)) =>
      `(def $name ($arg1 : $argTy1) ($arg2 : $argTy2) ($arg3 : $argTy3) (s s' : Verity.ContractState) : Prop :=
          Verity.Specs.storageMap2UpdateSpec
            $slotTerm $key1 $key2 $value
            (fun s s' => ($frame) s s' ∧ ($extra) s s') s s')
  | `(#gen_spec_transfer $name:ident for3
      ($fromAddr:ident : $fromTy:term) ($toAddr:ident : $toTy:term) ($amount:ident : $amountTy:term)
      ($slotTerm:term, $frame:term)) =>
      `(def $name ($fromAddr : $fromTy) ($toAddr : $toTy) ($amount : $amountTy) (s s' : Verity.ContractState) : Prop :=
          s.storageMap $slotTerm $fromAddr ≥ $amount ∧
          Verity.Specs.storageMapTransferSpec
            $slotTerm $fromAddr $toAddr $amount $frame s s')
  | `(#gen_spec_transfer_from $name:ident for4
      ($spender:ident : $spenderTy:term) ($fromAddr:ident : $fromTy:term) ($toAddr:ident : $toTy:term) ($amount:ident : $amountTy:term)
      ($balanceSlot:term, $allowanceSlot:term, $frame:term)) =>
      `(def $name ($spender : $spenderTy) ($fromAddr : $fromTy) ($toAddr : $toTy) ($amount : $amountTy) (s s' : Verity.ContractState) : Prop :=
          s.storageMap2 $allowanceSlot $fromAddr $spender ≥ $amount ∧
          s.storageMap $balanceSlot $fromAddr ≥ $amount ∧
          Verity.Specs.storageMapTransferFromSpec
            $balanceSlot $allowanceSlot $fromAddr $toAddr $spender $amount $frame s s')
  | `(#gen_spec_view $name:ident) =>
      `(def $name (s s' : Verity.ContractState) : Prop :=
          Verity.Specs.viewPreservesState s s')
  | `(#gen_spec_view $name:ident ($extra:term)) =>
      `(def $name (s s' : Verity.ContractState) : Prop :=
          Verity.Macro.viewFrameSpec $extra s s')
  | `(#gen_spec_view $name:ident for ($arg:ident : $argTy:term)) =>
      `(def $name ($arg : $argTy) (s s' : Verity.ContractState) : Prop :=
          Verity.Specs.viewPreservesState s s')
  | `(#gen_spec_view $name:ident for ($arg:ident : $argTy:term) ($extra:term)) =>
      `(def $name ($arg : $argTy) (s s' : Verity.ContractState) : Prop :=
          Verity.Macro.viewFrameSpec $extra s s')
  | `(#gen_spec_view $name:ident for2 ($arg1:ident : $argTy1:term) ($arg2:ident : $argTy2:term)) =>
      `(def $name ($arg1 : $argTy1) ($arg2 : $argTy2) (s s' : Verity.ContractState) : Prop :=
          Verity.Specs.viewPreservesState s s')
  | `(#gen_spec_view $name:ident for2 ($arg1:ident : $argTy1:term) ($arg2:ident : $argTy2:term)
      ($extra:term)) =>
      `(def $name ($arg1 : $argTy1) ($arg2 : $argTy2) (s s' : Verity.ContractState) : Prop :=
          Verity.Macro.viewFrameSpec $extra s s')

/-! ## Unified Parametric `#gen_fn_spec` Generator (`unchangedExcept` & `FnSpec`) -/

syntax (name := genFnSpecCmd)
  "#gen_fn_spec " ident " (" term ", " term ")" : command

syntax (name := genFnSpecCmdExtra)
  "#gen_fn_spec " ident " (" term ", " term ", " term ")" : command

syntax (name := genFnSpecCmdFor)
  "#gen_fn_spec " ident " for " "(" ident " : " term ")"
    " (" term ", " term ")" : command

syntax (name := genFnSpecCmdForExtra)
  "#gen_fn_spec " ident " for " "(" ident " : " term ")"
    " (" term ", " term ", " term ")" : command

syntax (name := genFnSpecCmdFor2)
  "#gen_fn_spec " ident " for2 " "(" ident " : " term ")" " (" ident " : " term ")"
    " (" term ", " term ")" : command

syntax (name := genFnSpecCmdFor2Extra)
  "#gen_fn_spec " ident " for2 " "(" ident " : " term ")" " (" ident " : " term ")"
    " (" term ", " term ", " term ")" : command

syntax (name := genFnSpecCmdFor3)
  "#gen_fn_spec " ident " for3 "
    "(" ident " : " term ")" " (" ident " : " term ")" " (" ident " : " term ")"
    " (" term ", " term ")" : command

syntax (name := genFnSpecCmdFor3Extra)
  "#gen_fn_spec " ident " for3 "
    "(" ident " : " term ")" " (" ident " : " term ")" " (" ident " : " term ")"
    " (" term ", " term ", " term ")" : command

syntax (name := genFnSpecCmdFor4)
  "#gen_fn_spec " ident " for4 "
    "(" ident " : " term ")" " (" ident " : " term ")" " (" ident " : " term ")" " (" ident " : " term ")"
    " (" term ", " term ")" : command

syntax (name := genFnSpecCmdFor4Extra)
  "#gen_fn_spec " ident " for4 "
    "(" ident " : " term ")" " (" ident " : " term ")" " (" ident " : " term ")" " (" ident " : " term ")"
    " (" term ", " term ", " term ")" : command

syntax (name := genFnSpecModifiesCmd)
  "#gen_fn_spec " ident " modifies " "[" term,* "]" " ensures " "(" term ")" : command

syntax (name := genFnSpecModifiesForCmd)
  "#gen_fn_spec " ident " for " "(" ident " : " term ")"
    " modifies " "[" term,* "]" " ensures " "(" term ")" : command

syntax (name := genFnSpecModifiesFor2Cmd)
  "#gen_fn_spec " ident " for2 " "(" ident " : " term ")" " (" ident " : " term ")"
    " modifies " "[" term,* "]" " ensures " "(" term ")" : command

syntax (name := genFnSpecWpCmd)
  "#gen_fn_spec " ident " [" term "]" " (" term ", " term ", " term ")" : command

syntax (name := genFnSpecWpEventsCmd)
  "#gen_fn_spec " ident " [" term "]" " (" term ", " term ", " term ", " term ")" : command

syntax (name := genFnSpecWpForCmd)
  "#gen_fn_spec " ident " for " "(" ident " : " term ")" " [" term "]"
    " (" term ", " term ", " term ")" : command

syntax (name := genFnSpecWpEventsForCmd)
  "#gen_fn_spec " ident " for " "(" ident " : " term ")" " [" term "]"
    " (" term ", " term ", " term ", " term ")" : command

syntax (name := genFnSpecWpFor2Cmd)
  "#gen_fn_spec " ident " for2 " "(" ident " : " term ")" " (" ident " : " term ")" " [" term "]"
    " (" term ", " term ", " term ")" : command

syntax (name := genFnSpecWpEventsFor2Cmd)
  "#gen_fn_spec " ident " for2 " "(" ident " : " term ")" " (" ident " : " term ")" " [" term "]"
    " (" term ", " term ", " term ", " term ")" : command

macro_rules
  | `(#gen_fn_spec $name:ident ($writes:term, $post:term)) =>
      `(def $name (s s' : Verity.ContractState) : Prop :=
          Verity.Specs.fnUpdateSpec $writes $post s s')
  | `(#gen_fn_spec $name:ident ($writes:term, $post:term, $extra:term)) =>
      `(def $name (s s' : Verity.ContractState) : Prop :=
          Verity.Specs.fnUpdateSpec $writes
            (fun s s' => ($post) s s' ∧ ($extra) s s') s s')
  | `(#gen_fn_spec $name:ident for ($arg:ident : $argTy:term)
      ($writes:term, $post:term)) =>
      `(def $name ($arg : $argTy) (s s' : Verity.ContractState) : Prop :=
          Verity.Specs.fnUpdateSpec $writes $post s s')
  | `(#gen_fn_spec $name:ident for ($arg:ident : $argTy:term)
      ($writes:term, $post:term, $extra:term)) =>
      `(def $name ($arg : $argTy) (s s' : Verity.ContractState) : Prop :=
          Verity.Specs.fnUpdateSpec $writes
            (fun s s' => ($post) s s' ∧ ($extra) s s') s s')
  | `(#gen_fn_spec $name:ident for2 ($arg1:ident : $argTy1:term) ($arg2:ident : $argTy2:term)
      ($writes:term, $post:term)) =>
      `(def $name ($arg1 : $argTy1) ($arg2 : $argTy2) (s s' : Verity.ContractState) : Prop :=
          Verity.Specs.fnUpdateSpec $writes $post s s')
  | `(#gen_fn_spec $name:ident for2 ($arg1:ident : $argTy1:term) ($arg2:ident : $argTy2:term)
      ($writes:term, $post:term, $extra:term)) =>
      `(def $name ($arg1 : $argTy1) ($arg2 : $argTy2) (s s' : Verity.ContractState) : Prop :=
          Verity.Specs.fnUpdateSpec $writes
            (fun s s' => ($post) s s' ∧ ($extra) s s') s s')
  | `(#gen_fn_spec $name:ident for3
      ($arg1:ident : $argTy1:term) ($arg2:ident : $argTy2:term) ($arg3:ident : $argTy3:term)
      ($writes:term, $post:term)) =>
      `(def $name ($arg1 : $argTy1) ($arg2 : $argTy2) ($arg3 : $argTy3)
          (s s' : Verity.ContractState) : Prop :=
          Verity.Specs.fnUpdateSpec $writes $post s s')
  | `(#gen_fn_spec $name:ident for3
      ($arg1:ident : $argTy1:term) ($arg2:ident : $argTy2:term) ($arg3:ident : $argTy3:term)
      ($writes:term, $post:term, $extra:term)) =>
      `(def $name ($arg1 : $argTy1) ($arg2 : $argTy2) ($arg3 : $argTy3)
          (s s' : Verity.ContractState) : Prop :=
          Verity.Specs.fnUpdateSpec $writes
            (fun s s' => ($post) s s' ∧ ($extra) s s') s s')
  | `(#gen_fn_spec $name:ident for4
      ($arg1:ident : $argTy1:term) ($arg2:ident : $argTy2:term)
      ($arg3:ident : $argTy3:term) ($arg4:ident : $argTy4:term)
      ($writes:term, $post:term)) =>
      `(def $name ($arg1 : $argTy1) ($arg2 : $argTy2) ($arg3 : $argTy3) ($arg4 : $argTy4)
          (s s' : Verity.ContractState) : Prop :=
          Verity.Specs.fnUpdateSpec $writes $post s s')
  | `(#gen_fn_spec $name:ident for4
      ($arg1:ident : $argTy1:term) ($arg2:ident : $argTy2:term)
      ($arg3:ident : $argTy3:term) ($arg4:ident : $argTy4:term)
      ($writes:term, $post:term, $extra:term)) =>
      `(def $name ($arg1 : $argTy1) ($arg2 : $argTy2) ($arg3 : $argTy3) ($arg4 : $argTy4)
          (s s' : Verity.ContractState) : Prop :=
          Verity.Specs.fnUpdateSpec $writes
            (fun s s' => ($post) s s' ∧ ($extra) s s') s s')
  | `(#gen_fn_spec $name:ident modifies [ $[$writes:term],* ] ensures ($post:term)) => do
      let writeKeys ← writes.mapM fun w => `(Verity.Specs.ToSpecStorageKey.toSpecStorageKey $w)
      `(def $name (s s' : Verity.ContractState) : Prop :=
          Verity.Specs.fnUpdateSpec [ $[$writeKeys],* ] $post s s')
  | `(#gen_fn_spec $name:ident for ($arg:ident : $argTy:term)
      modifies [ $[$writes:term],* ] ensures ($post:term)) => do
      let writeKeys ← writes.mapM fun w => `(Verity.Specs.ToSpecStorageKey.toSpecStorageKey $w)
      `(def $name ($arg : $argTy) (s s' : Verity.ContractState) : Prop :=
          Verity.Specs.fnUpdateSpec [ $[$writeKeys],* ] $post s s')
  | `(#gen_fn_spec $name:ident for2 ($arg1:ident : $argTy1:term) ($arg2:ident : $argTy2:term)
      modifies [ $[$writes:term],* ] ensures ($post:term)) => do
      let writeKeys ← writes.mapM fun w => `(Verity.Specs.ToSpecStorageKey.toSpecStorageKey $w)
      `(def $name ($arg1 : $argTy1) ($arg2 : $argTy2) (s s' : Verity.ContractState) : Prop :=
          Verity.Specs.fnUpdateSpec [ $[$writeKeys],* ] $post s s')
  | `(#gen_fn_spec $name:ident [$retTy:term] ($writes:term, $pre:term, $post:term)) =>
      `(def $name (s : Verity.ContractState) : Verity.Specs.FnSpec $retTy :=
          { pre := ($pre) s
            post := ($post) s
            writes := $writes })
  | `(#gen_fn_spec $name:ident [$retTy:term] ($writes:term, $pre:term, $post:term, $events:term)) =>
      `(def $name (s : Verity.ContractState) : Verity.Specs.FnSpec $retTy :=
          { pre := ($pre) s
            post := ($post) s
            events := ($events) s
            writes := $writes })
  | `(#gen_fn_spec $name:ident for ($arg:ident : $argTy:term) [$retTy:term]
      ($writes:term, $pre:term, $post:term)) =>
      `(def $name ($arg : $argTy) (s : Verity.ContractState) : Verity.Specs.FnSpec $retTy :=
          { pre := ($pre) s
            post := ($post) s
            writes := $writes })
  | `(#gen_fn_spec $name:ident for ($arg:ident : $argTy:term) [$retTy:term]
      ($writes:term, $pre:term, $post:term, $events:term)) =>
      `(def $name ($arg : $argTy) (s : Verity.ContractState) : Verity.Specs.FnSpec $retTy :=
          { pre := ($pre) s
            post := ($post) s
            events := ($events) s
            writes := $writes })
  | `(#gen_fn_spec $name:ident for2 ($arg1:ident : $argTy1:term) ($arg2:ident : $argTy2:term) [$retTy:term]
      ($writes:term, $pre:term, $post:term)) =>
      `(def $name ($arg1 : $argTy1) ($arg2 : $argTy2) (s : Verity.ContractState) :
          Verity.Specs.FnSpec $retTy :=
          { pre := ($pre) s
            post := ($post) s
            writes := $writes })
  | `(#gen_fn_spec $name:ident for2 ($arg1:ident : $argTy1:term) ($arg2:ident : $argTy2:term) [$retTy:term]
      ($writes:term, $pre:term, $post:term, $events:term)) =>
      `(def $name ($arg1 : $argTy1) ($arg2 : $argTy2) (s : Verity.ContractState) :
          Verity.Specs.FnSpec $retTy :=
          { pre := ($pre) s
            post := ($post) s
            events := ($events) s
            writes := $writes })

/-- Build a right-nested conjunction of `PreservesSlot.preserved` assertions over `preserves`. -/
def mkPreservesConjuncts (preserves : Array (TSyntax `term)) : MacroM (TSyntax `term) := do
  if preserves.isEmpty then
    `(True)
  else
    let mut body ← `(Verity.Macro.PreservesSlot.preserved $(preserves.back!) s s')
    for idx in (List.range (preserves.size - 1)).reverse do
      let item := preserves[idx]!
      body ← `(Verity.Macro.PreservesSlot.preserved $item s s' ∧ $body)
    Pure.pure body

/-- Extract `simpLemma` syntax from a term when it is an identifier. -/
def termSimpLemmas (terms : Array (TSyntax `term)) :
    MacroM (Array (TSyntax `Lean.Parser.Tactic.simpLemma)) := do
  let mut out : Array (TSyntax `Lean.Parser.Tactic.simpLemma) := #[]
  for t in terms do
    match t with
    | `($id:ident) =>
        out := out.push (← `(Lean.Parser.Tactic.simpLemma| $id:ident))
    | _ => Pure.pure ()
  Pure.pure out

/-- Generate `<fn>_writes_mask`, `<fn>_preserves_mask`, `<fn>_footprint_disjoint`,
`<fn>_preserves_spec`, and the auto-proved `<fn>_preserves_frame` theorem. -/
def mkAutoFrameSpecDecls
    (fn : Ident)
    (params : Array (Ident × TSyntax `term))
    (writes : Array (TSyntax `term))
    (preserves : Array (TSyntax `term))
    (extraSlotIdents : Array Ident := #[]) :
    MacroM (Array (TSyntax `command)) := do
  let baseName := fn.getId.eraseMacroScopes
  let writesMaskName := mkIdent (baseName.appendAfter "_writes_mask")
  let preservesMaskName := mkIdent (baseName.appendAfter "_preserves_mask")
  let disjointThmName := mkIdent (baseName.appendAfter "_footprint_disjoint")
  let preservesSpecName := mkIdent (baseName.appendAfter "_preserves_spec")
  let preservesFrameName := mkIdent (baseName.appendAfter "_preserves_frame")
  let writesIndices ← writes.mapM fun w => `(Verity.Macro.PreservesSlot.slotIndex $w)
  let preservesIndices ← preserves.mapM fun p => `(Verity.Macro.PreservesSlot.slotIndex $p)
  let preservesBody ← mkPreservesConjuncts preserves
  let mut fnApp : TSyntax `term := mkIdent baseName
  for (pid, _) in params do
    let cleanPid : TSyntax `term := mkIdent pid.getId
    fnApp ← `($fnApp $cleanPid)
  let mut frameProp ← `($preservesSpecName s (($fnApp).run s).snd)
  frameProp ← `(∀ (s : Verity.ContractState), $frameProp)
  for (pid, pty) in params.reverse do
    let cleanPid := mkIdent pid.getId
    frameProp ← `(∀ ($cleanPid : $pty), $frameProp)
  let fnIdent := mkIdent baseName
  let fnSimp ← `(Lean.Parser.Tactic.simpLemma| $fnIdent:ident)
  let specSimp ← `(Lean.Parser.Tactic.simpLemma| $preservesSpecName:ident)
  let slotSimps ← termSimpLemmas (writes ++ preserves)
  let extraSimps ← extraSlotIdents.mapM fun id => `(Lean.Parser.Tactic.simpLemma| $id:ident)
  let allSimps := #[fnSimp, specSimp] ++ slotSimps ++ extraSimps
  let cmd1 ← `(command|
    def $writesMaskName : Nat :=
      Verity.Macro.slotsToBitmask [ $[$writesIndices],* ])
  let cmd2 ← `(command|
    def $preservesMaskName : Nat :=
      Verity.Macro.slotsToBitmask [ $[$preservesIndices],* ])
  let cmd3 ← `(command|
    @[simp] theorem $disjointThmName :
        Verity.Macro.bitmaskDisjoint $writesMaskName $preservesMaskName = true := by
      decide)
  let cmd4 ← `(command|
    set_option linter.unusedVariables false in
    def $preservesSpecName (s s' : Verity.ContractState) : Prop :=
      $preservesBody)
  let cmd5 ← `(command|
    set_option linter.unusedVariables false in
    theorem $preservesFrameName : $frameProp := by
      verity_frame_auto [ $[$allSimps],* ])
  Pure.pure #[cmd1, cmd2, cmd3, cmd4, cmd5]

/-- Generate `<fn>_ensures_spec` and `<fn>_meets_ensures` from declarative
`requires_clause(...)`, `ensures_clause(...)`, and `ensures(...)` annotations. -/
def mkDeclarativeSpecDecls
    (fn : Ident)
    (params : Array (Ident × TSyntax `term))
    (specClauses : Array (TSyntax `veritySpecClause))
    (slotIdents : Array Ident) :
    MacroM (Array (TSyntax `command)) := do
  let mut reqTerms : Array (TSyntax `term) := #[]
  let mut ensTerms : Array (TSyntax `term) := #[]
  for clause in specClauses do
    match clause with
    | `(veritySpecClause| requires_clause($req:term)) =>
        reqTerms := reqTerms.push req
    | `(veritySpecClause| ensures_clause($ens:term)) =>
        ensTerms := ensTerms.push ens
    | `(veritySpecClause| ensures($ens:term)) =>
        ensTerms := ensTerms.push ens
    | _ => Pure.pure ()
  let mut postBody : TSyntax `term ← `(True)
  if !ensTerms.isEmpty then
    postBody := ensTerms.back!
    for idx in (List.range (ensTerms.size - 1)).reverse do
      postBody ← `($(ensTerms[idx]!) ∧ $postBody)
  for req in reqTerms.reverse do
    postBody ← `($req → $postBody)
  let baseName := fn.getId.eraseMacroScopes
  let ensuresSpecName := mkIdent (baseName.appendAfter "_ensures_spec")
  let meetsEnsuresName := mkIdent (baseName.appendAfter "_meets_ensures")
  let mut fnApp : TSyntax `term := mkIdent baseName
  let mut specApp : TSyntax `term := ensuresSpecName
  for (pid, _) in params do
    let cleanPid : TSyntax `term := mkIdent pid.getId
    fnApp ← `($fnApp $cleanPid)
    specApp ← `($specApp $cleanPid)
  let mut specType ← `(Verity.ContractState → Verity.ContractState → Prop)
  let mut specVal ← `(fun (s s' : Verity.ContractState) => $postBody)
  let mut thmProp ← `($specApp s (($fnApp).run s).snd)
  thmProp ← `(∀ (s : Verity.ContractState), $thmProp)
  for (pid, pty) in params.reverse do
    let cleanPid := mkIdent pid.getId
    specType ← `($pty → $specType)
    specVal ← `(fun ($cleanPid : $pty) => $specVal)
    thmProp ← `(∀ ($cleanPid : $pty), $thmProp)
  let fnIdent := mkIdent baseName
  let fnSimp ← `(Lean.Parser.Tactic.simpLemma| $fnIdent:ident)
  let specSimp ← `(Lean.Parser.Tactic.simpLemma| $ensuresSpecName:ident)
  let slotSimps ← slotIdents.mapM fun id => `(Lean.Parser.Tactic.simpLemma| $id:ident)
  let allSimps := #[fnSimp, specSimp] ++ slotSimps
  let cmd1 ← `(command|
    set_option linter.unusedVariables false in
    def $ensuresSpecName : $specType :=
      $specVal)
  let cmd2 ← `(command|
    set_option linter.unusedVariables false in
    theorem $meetsEnsuresName : $thmProp := by
      verity_auto [ $[$allSimps],* ])
  Pure.pure #[cmd1, cmd2]

syntax (name := genAutoFrameSpecCmd)
  "#gen_auto_frame_spec " ident " modifies " "[" term,* "]"
    " preserves " "[" term,* "]" : command

syntax (name := genAutoFrameSpecForCmd)
  "#gen_auto_frame_spec " ident " for " "(" ident " : " term ")"
    " modifies " "[" term,* "]" " preserves " "[" term,* "]" : command

syntax (name := genAutoFrameSpecFor2Cmd)
  "#gen_auto_frame_spec " ident " for2 " "(" ident " : " term ")" " (" ident " : " term ")"
    " modifies " "[" term,* "]" " preserves " "[" term,* "]" : command

macro_rules
  | `(#gen_auto_frame_spec $fn:ident modifies [ $[$writes:term],* ] preserves [ $[$presSlots:term],* ]) => do
      let cmds ← mkAutoFrameSpecDecls fn #[] writes presSlots
      Pure.pure (mkNullNode (cmds.map (·.raw)))
  | `(#gen_auto_frame_spec $fn:ident for ($arg:ident : $argTy:term)
      modifies [ $[$writes:term],* ] preserves [ $[$presSlots:term],* ]) => do
      let cmds ← mkAutoFrameSpecDecls fn #[(arg, argTy)] writes presSlots
      Pure.pure (mkNullNode (cmds.map (·.raw)))
  | `(#gen_auto_frame_spec $fn:ident for2 ($arg1:ident : $argTy1:term) ($arg2:ident : $argTy2:term)
      modifies [ $[$writes:term],* ] preserves [ $[$presSlots:term],* ]) => do
      let cmds ← mkAutoFrameSpecDecls fn #[(arg1, argTy1), (arg2, argTy2)] writes presSlots
      Pure.pure (mkNullNode (cmds.map (·.raw)))

/-- Parse `verityParam` syntax into `(Ident × Term)` pairs for declarative spec generation. -/
def parseVerityParamsForSpec (params : Array (TSyntax `verityParam)) :
    MacroM (Array (Ident × TSyntax `term)) :=
  params.mapM fun p =>
    match p with
    | `(verityParam| $name:ident : $ty:term) => Pure.pure (name, ty)
    | _ => Macro.throwUnsupported

/-- Extract storage field identifiers from optional `verityModifies` syntax. -/
def extractModifiesIdents? (modClause? : Option (TSyntax `verityModifies)) :
    Array Ident :=
  match modClause? with
  | none => #[]
  | some stx =>
      match stx with
      | `(verityModifies| modifies($[$fields:ident],*)) => fields
      | _ => #[]

/-- Extract storage field identifiers from optional `verityPreserves` syntax. -/
def extractPreservesIdents? (presClause? : Option (TSyntax `verityPreserves)) :
    Array Ident :=
  match presClause? with
  | none => #[]
  | some stx =>
      match stx with
      | `(verityPreserves| preserves($[$fields:ident],*)) => fields
      | _ => #[]

/-- Extract all storage field identifiers declared in a `verity_contract` storage block. -/
def extractStorageFieldIdents (items : Array (TSyntax `verityStorageItem)) :
    Array Ident := Id.run do
  let mut out : Array Ident := #[]
  for item in items do
    match item with
    | `(verityStorageItem| $name:ident : $_ty:term := slot $_n:num) =>
        out := out.push name
    | `(verityStorageItem| transient $name:ident : $_ty:term := slot $_n:num) =>
        out := out.push name
    | _ => Pure.pure ()
  return out

macro_rules
  | `(command| verity_contract $contractName:ident $[is $[$parentNames:ident],*]? $[include $[$includeNames:ident],*]? where $[types $[$newtypeDecls:verityNewtype]*]? $[enums $[$enumDecls:verityEnumDecl]*]? $[inductive $[$adtDecls:verityAdtDecl]*]? $[$nsSpec:verityNamespaceSpec]? storage $[$storageItems:verityStorageItem]* $[roles $[$roleDecls:verityRoleDecl]*]? $[$structDecls:verityStructDecl]* $[errors $[$errorDecls:verityError]*]? $[event_defs $[$eventDecls:verityEvent]*]? $[constants $[$constantDecls:verityConstant]*]? $[immutables $[$immutableDecls:verityImmutable]*]? $[interfaces $[$interfaceDecls:verityInterface]*]? $[linked_contracts $[$linkedDecls:verityLinkedContract]*]? $[linked_externals $[$externalDecls:verityExternal]*]? $[$ctor:verityConstructor]? $[$entrypoints:veritySpecialEntrypoint]* $[$modifierDecls:verityModifier]* $[$functions:verityFunction]*) => do
      let allStorageFields := extractStorageFieldIdents storageItems
      let mut strippedFunctions : Array (TSyntax `verityFunction) := #[]
      let mut autoSpecCmds : Array (TSyntax `command) := #[]
      let mut hasDeclarative := false
      for fnStx in functions do
        match fnStx with
        | `(verityFunction| function $[$modsBefore:verityMutability]* $[$pureMod?:pureMutabilityMarker]? $[$modsAfter:verityMutability]* $[$dispatch:verityDispatch]* $name:ident ($[$params:verityParam],*) $[$guard?:verityInitGuard]? $[$modifierUse?:verityModifierUse]? $[$requiresRoleClause?:verityRequiresRole]? $[$modifiesClause?:verityModifies]? $[$preservesClause?:verityPreserves]? $[$specClauses:veritySpecClause]* $[$localObligations?:verityLocalObligations]? : $retTy:term := $body:term) =>
            if preservesClause?.isSome || !specClauses.isEmpty then
              hasDeclarative := true
              let strippedFn ← `(verityFunction| function $[$modsBefore:verityMutability]* $[$pureMod?:pureMutabilityMarker]? $[$modsAfter:verityMutability]* $[$dispatch:verityDispatch]* $name:ident ($[$params:verityParam],*) $[$guard?:verityInitGuard]? $[$modifierUse?:verityModifierUse]? $[$requiresRoleClause?:verityRequiresRole]? $[$modifiesClause?:verityModifies]? $[$localObligations?:verityLocalObligations]? : $retTy:term := $body:term)
              strippedFunctions := strippedFunctions.push strippedFn
              let parsedParams ← parseVerityParamsForSpec params
              let modIdents := extractModifiesIdents? modifiesClause?
              let presIdents := extractPreservesIdents? preservesClause?
              if preservesClause?.isSome then
                let writeTerms : Array (TSyntax `term) := modIdents.map fun id => ⟨id.raw⟩
                let presTerms : Array (TSyntax `term) := presIdents.map fun id => ⟨id.raw⟩
                let frameDecls ← mkAutoFrameSpecDecls name parsedParams writeTerms presTerms allStorageFields
                autoSpecCmds := autoSpecCmds ++ frameDecls
              if !specClauses.isEmpty then
                let specDecls ← mkDeclarativeSpecDecls name parsedParams specClauses
                  (allStorageFields ++ modIdents ++ presIdents)
                autoSpecCmds := autoSpecCmds ++ specDecls
            else
              strippedFunctions := strippedFunctions.push fnStx
        | _ =>
            strippedFunctions := strippedFunctions.push fnStx
      if !hasDeclarative then
        Macro.throwUnsupported
      else
        let contractCmd ← `(command|
          verity_contract $contractName:ident $[is $[$parentNames:ident],*]? $[include $[$includeNames:ident],*]? where $[types $[$newtypeDecls:verityNewtype]*]? $[enums $[$enumDecls:verityEnumDecl]*]? $[inductive $[$adtDecls:verityAdtDecl]*]? $[$nsSpec:verityNamespaceSpec]? storage $[$storageItems:verityStorageItem]* $[roles $[$roleDecls:verityRoleDecl]*]? $[$structDecls:verityStructDecl]* $[errors $[$errorDecls:verityError]*]? $[event_defs $[$eventDecls:verityEvent]*]? $[constants $[$constantDecls:verityConstant]*]? $[immutables $[$immutableDecls:verityImmutable]*]? $[interfaces $[$interfaceDecls:verityInterface]*]? $[linked_contracts $[$linkedDecls:verityLinkedContract]*]? $[linked_externals $[$externalDecls:verityExternal]*]? $[$ctor:verityConstructor]? $[$entrypoints:veritySpecialEntrypoint]* $[$modifierDecls:verityModifier]* $[$strippedFunctions:verityFunction]*)
        let nsOpenCmd ← `(command| namespace $contractName)
        let nsCloseCmd ← `(command| end $contractName)
        let allCmds := #[contractCmd, nsOpenCmd] ++ autoSpecCmds ++ #[nsCloseCmd]
        Pure.pure (mkNullNode (allCmds.map (·.raw)))

/-! ### Verified `#gen_fn_spec` Witnesses (`unchangedExcept` & `FnSpec.Satisfies`) -/

#gen_fn_spec canonicalSlotFnSpec for (val : Verity.Uint256)
  ([Verity.Specs.SpecStorageKey.slot 0],
   fun _ s' => s'.storage 0 = val)

#gen_fn_spec canonicalGuardedSlotWpSpec for (val : Verity.Uint256) [Unit]
  ([Verity.Specs.SpecStorageKey.slot 0],
   fun s => s.sender = s.storageAddr 1,
   fun _ _ s' => s'.storage 0 = val)

theorem canonicalSlotFnSpec_satisfied
    (val : Verity.Uint256) (s : Verity.ContractState) :
    canonicalSlotFnSpec val s ((Verity.setStorage ⟨0⟩ val).run s).snd := by
  simp [canonicalSlotFnSpec, Verity.Specs.fnUpdateSpec]

theorem canonicalGuardedSlotWpSpec_satisfies
    (val : Verity.Uint256) (s : Verity.ContractState) :
    Verity.Specs.FnSpec.Satisfies
      (Verity.bind
        (Verity.require (s.sender == s.storageAddr 1) "unauthorized")
        (fun _ => Verity.setStorage ⟨0⟩ val))
      s
      (canonicalGuardedSlotWpSpec val s) := by
  unfold Verity.Specs.FnSpec.Satisfies canonicalGuardedSlotWpSpec
  by_cases h : s.sender = s.storageAddr 1
  · simp [bind_require_eq, Verity.Contract.run, Verity.setStorage, h]
  · simp [bind_require_eq, Verity.Contract.run, h]

end Verity.Macro
