import Verity.Specs.Common
import Verity.Macro.EffectAnalysis

namespace Verity.Macro

set_option hygiene false

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
  | `(#gen_spec $name:ident ($slot:term, $value:term, $frame:term)) =>
      `(def $name (s s' : Verity.ContractState) : Prop :=
          Verity.Specs.storageUpdateSpec $slot $value $frame s s')
  | `(#gen_spec $name:ident ($slot:term, $value:term, $frame:term, $extra:term)) =>
      `(def $name (s s' : Verity.ContractState) : Prop :=
          Verity.Specs.storageUpdateSpec $slot $value
            (fun s s' => ($frame) s s' ∧ ($extra) s s') s s')
  | `(#gen_spec_addr $name:ident ($slot:term, $value:term, $frame:term)) =>
      `(def $name (s s' : Verity.ContractState) : Prop :=
          Verity.Specs.storageAddrUpdateSpec $slot $value $frame s s')
  | `(#gen_spec_addr $name:ident ($slot:term, $value:term, $frame:term, $extra:term)) =>
      `(def $name (s s' : Verity.ContractState) : Prop :=
          Verity.Specs.storageAddrUpdateSpec $slot $value
            (fun s s' => ($frame) s s' ∧ ($extra) s s') s s')
  | `(#gen_spec $name:ident for ($arg:ident : $argTy:term) ($slot:term, $value:term, $frame:term)) =>
      `(def $name ($arg : $argTy) (s s' : Verity.ContractState) : Prop :=
          Verity.Specs.storageUpdateSpec $slot $value $frame s s')
  | `(#gen_spec $name:ident for ($arg:ident : $argTy:term) ($slot:term, $value:term, $frame:term, $extra:term)) =>
      `(def $name ($arg : $argTy) (s s' : Verity.ContractState) : Prop :=
          Verity.Specs.storageUpdateSpec $slot $value
            (fun s s' => ($frame) s s' ∧ ($extra) s s') s s')
  | `(#gen_spec $name:ident for2 ($arg1:ident : $argTy1:term) ($arg2:ident : $argTy2:term)
      ($slot:term, $value:term, $frame:term)) =>
      `(def $name ($arg1 : $argTy1) ($arg2 : $argTy2) (s s' : Verity.ContractState) : Prop :=
          Verity.Specs.storageUpdateSpec $slot $value $frame s s')
  | `(#gen_spec $name:ident for2 ($arg1:ident : $argTy1:term) ($arg2:ident : $argTy2:term)
      ($slot:term, $value:term, $frame:term, $extra:term)) =>
      `(def $name ($arg1 : $argTy1) ($arg2 : $argTy2) (s s' : Verity.ContractState) : Prop :=
          Verity.Specs.storageUpdateSpec $slot $value
            (fun s s' => ($frame) s s' ∧ ($extra) s s') s s')
  | `(#gen_spec_addr $name:ident for ($arg:ident : $argTy:term) ($slot:term, $value:term, $frame:term)) =>
      `(def $name ($arg : $argTy) (s s' : Verity.ContractState) : Prop :=
          Verity.Specs.storageAddrUpdateSpec $slot $value $frame s s')
  | `(#gen_spec_addr $name:ident for ($arg:ident : $argTy:term) ($slot:term, $value:term, $frame:term, $extra:term)) =>
      `(def $name ($arg : $argTy) (s s' : Verity.ContractState) : Prop :=
          Verity.Specs.storageAddrUpdateSpec $slot $value
            (fun s s' => ($frame) s s' ∧ ($extra) s s') s s')
  | `(#gen_spec_addr $name:ident for2 ($arg1:ident : $argTy1:term) ($arg2:ident : $argTy2:term)
      ($slot:term, $value:term, $frame:term)) =>
      `(def $name ($arg1 : $argTy1) ($arg2 : $argTy2) (s s' : Verity.ContractState) : Prop :=
          Verity.Specs.storageAddrUpdateSpec $slot $value $frame s s')
  | `(#gen_spec_addr $name:ident for2 ($arg1:ident : $argTy1:term) ($arg2:ident : $argTy2:term)
      ($slot:term, $value:term, $frame:term, $extra:term)) =>
      `(def $name ($arg1 : $argTy1) ($arg2 : $argTy2) (s s' : Verity.ContractState) : Prop :=
          Verity.Specs.storageAddrUpdateSpec $slot $value
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
      ($slot:term, $key:term, $value:term, $frame:term)) =>
      `(def $name (s s' : Verity.ContractState) : Prop :=
          Verity.Specs.storageMapUpdateSpec
            $slot $key $value $frame s s')
  | `(#gen_spec_map $name:ident
      ($slot:term, $key:term, $value:term, $frame:term, $extra:term)) =>
      `(def $name (s s' : Verity.ContractState) : Prop :=
          Verity.Specs.storageMapUpdateSpec
            $slot $key $value
            (fun s s' => ($frame) s s' ∧ ($extra) s s') s s')
  | `(#gen_spec_map $name:ident for ($arg:ident : $argTy:term)
      ($mapSlot:term, $key:term, $value:term, $frame:term)) =>
      `(def $name ($arg : $argTy) (s s' : Verity.ContractState) : Prop :=
          Verity.Specs.storageMapUpdateSpec
            $mapSlot $key $value $frame s s')
  | `(#gen_spec_map $name:ident for ($arg:ident : $argTy:term)
      ($slot:term, $key:term, $value:term, $frame:term, $extra:term)) =>
      `(def $name ($arg : $argTy) (s s' : Verity.ContractState) : Prop :=
          Verity.Specs.storageMapUpdateSpec
            $slot $key $value
            (fun s s' => ($frame) s s' ∧ ($extra) s s') s s')
  | `(#gen_spec_map $name:ident for2 ($arg1:ident : $argTy1:term) ($arg2:ident : $argTy2:term)
      ($slot:term, $key:term, $value:term, $frame:term)) =>
      `(def $name ($arg1 : $argTy1) ($arg2 : $argTy2) (s s' : Verity.ContractState) : Prop :=
          Verity.Specs.storageMapUpdateSpec
            $slot $key $value $frame s s')
  | `(#gen_spec_map $name:ident for2 ($arg1:ident : $argTy1:term) ($arg2:ident : $argTy2:term)
      ($slot:term, $key:term, $value:term, $frame:term, $extra:term)) =>
      `(def $name ($arg1 : $argTy1) ($arg2 : $argTy2) (s s' : Verity.ContractState) : Prop :=
          Verity.Specs.storageMapUpdateSpec
            $slot $key $value
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
      ($slot:term, $key1:term, $key2:term, $value:term, $frame:term)) =>
      `(def $name (s s' : Verity.ContractState) : Prop :=
          Verity.Specs.storageMap2UpdateSpec
            $slot $key1 $key2 $value $frame s s')
  | `(#gen_spec_map2 $name:ident
      ($slot:term, $key1:term, $key2:term, $value:term, $frame:term, $extra:term)) =>
      `(def $name (s s' : Verity.ContractState) : Prop :=
          Verity.Specs.storageMap2UpdateSpec
            $slot $key1 $key2 $value
            (fun s s' => ($frame) s s' ∧ ($extra) s s') s s')
  | `(#gen_spec_map2 $name:ident for ($arg:ident : $argTy:term)
      ($slot:term, $key1:term, $key2:term, $value:term, $frame:term)) =>
      `(def $name ($arg : $argTy) (s s' : Verity.ContractState) : Prop :=
          Verity.Specs.storageMap2UpdateSpec
            $slot $key1 $key2 $value $frame s s')
  | `(#gen_spec_map2 $name:ident for ($arg:ident : $argTy:term)
      ($slot:term, $key1:term, $key2:term, $value:term, $frame:term, $extra:term)) =>
      `(def $name ($arg : $argTy) (s s' : Verity.ContractState) : Prop :=
          Verity.Specs.storageMap2UpdateSpec
            $slot $key1 $key2 $value
            (fun s s' => ($frame) s s' ∧ ($extra) s s') s s')
  | `(#gen_spec_map2 $name:ident for2 ($arg1:ident : $argTy1:term) ($arg2:ident : $argTy2:term)
      ($slot:term, $key1:term, $key2:term, $value:term, $frame:term)) =>
      `(def $name ($arg1 : $argTy1) ($arg2 : $argTy2) (s s' : Verity.ContractState) : Prop :=
          Verity.Specs.storageMap2UpdateSpec
            $slot $key1 $key2 $value $frame s s')
  | `(#gen_spec_map2 $name:ident for2 ($arg1:ident : $argTy1:term) ($arg2:ident : $argTy2:term)
      ($slot:term, $key1:term, $key2:term, $value:term, $frame:term, $extra:term)) =>
      `(def $name ($arg1 : $argTy1) ($arg2 : $argTy2) (s s' : Verity.ContractState) : Prop :=
          Verity.Specs.storageMap2UpdateSpec
            $slot $key1 $key2 $value
            (fun s s' => ($frame) s s' ∧ ($extra) s s') s s')
  | `(#gen_spec_map2 $name:ident for3
      ($arg1:ident : $argTy1:term) ($arg2:ident : $argTy2:term) ($arg3:ident : $argTy3:term)
      ($slot:term, $key1:term, $key2:term, $value:term, $frame:term)) =>
      `(def $name ($arg1 : $argTy1) ($arg2 : $argTy2) ($arg3 : $argTy3) (s s' : Verity.ContractState) : Prop :=
          Verity.Specs.storageMap2UpdateSpec
            $slot $key1 $key2 $value $frame s s')
  | `(#gen_spec_map2 $name:ident for3
      ($arg1:ident : $argTy1:term) ($arg2:ident : $argTy2:term) ($arg3:ident : $argTy3:term)
      ($slot:term, $key1:term, $key2:term, $value:term, $frame:term, $extra:term)) =>
      `(def $name ($arg1 : $argTy1) ($arg2 : $argTy2) ($arg3 : $argTy3) (s s' : Verity.ContractState) : Prop :=
          Verity.Specs.storageMap2UpdateSpec
            $slot $key1 $key2 $value
            (fun s s' => ($frame) s s' ∧ ($extra) s s') s s')
  | `(#gen_spec_transfer $name:ident for3
      ($fromAddr:ident : $fromTy:term) ($toAddr:ident : $toTy:term) ($amount:ident : $amountTy:term)
      ($slot:term, $frame:term)) =>
      `(def $name ($fromAddr : $fromTy) ($toAddr : $toTy) ($amount : $amountTy) (s s' : Verity.ContractState) : Prop :=
          s.storageMap $slot $fromAddr ≥ $amount ∧
          Verity.Specs.storageMapTransferSpec
            $slot $fromAddr $toAddr $amount $frame s s')
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

end Verity.Macro
