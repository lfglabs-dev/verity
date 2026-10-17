import Compiler.Proofs.IRGeneration.ImportedPrefixFrames
import Compiler.Proofs.IRGeneration.NativeSourceMappingWrites

namespace Compiler.Proofs.IRGeneration.ImportedMappingEffect
open Compiler.CompilationModel Compiler.CompilationModel.Denote CreationMemoryFrames

/-- Memory erasure commutes with the exact flat storage update, including every
other typed channel, account, event and environment field. -/
theorem erase_write (world : Verity.ContractState) (slot : Nat) (value : Verity.Core.Uint256) :
    eraseMemory (world.writeSlot slot value) = (eraseMemory world).writeSlot slot value := rfl

/-- Complete state effect of a persistent one-slot, unpacked mapping member. -/
theorem singleton_write (oracle : DenoteOracle) (fields : List Field) (name : String)
    (world : Verity.ContractState) (base key value : Nat)
    (persistent : fieldIsTransient fields name = false) :
    writeAddressKeyedMappingWordFieldSlots oracle fields name world [base] key 0 value =
      world.writeSlot (wordNormalize (oracle.mappingSlot base key)) (Verity.Core.Uint256.ofNat value) := by
  simp only [writeAddressKeyedMappingWordFieldSlots, List.map_cons, List.map_nil,
    Nat.add_zero, writeMappingTargets, persistent, Bool.false_eq_true, if_false]
  rw [SolidityImport.normalize_normalize]
  exact NativeSourceMappingWrites.writeSlots_single _ _ _

/-- Independent worlds retain their own memory and perform the same entire
nonmemory update. This is world equality, not a finite slot sample. -/
theorem write_related (left right : Verity.ContractState) (slot : Nat)
    (value : Verity.Core.Uint256) (same : Related left right) :
    Related (left.writeSlot slot value) (right.writeSlot slot value) := by
  change eraseMemory (left.writeSlot slot value) = eraseMemory (right.writeSlot slot value)
  rw [erase_write, erase_write, same]

/-- The actual Denote statement has the same complete write as the native
flat-storage bridge when field layout and evaluated operands are established. -/
theorem resolved_member_write (oracle : DenoteOracle) (fields : List Field)
    (state : DenoteState) (name memberName : String) (key value : Expr)
    (base resolvedKey resolvedValue : Nat) (members : List StructMember) (member : StructMember)
    (slots : findFieldWriteSlots fields name = some [base])
    (layout : findStructMembers fields name = some members)
    (found : findStructMember members memberName = some member)
    (offset : member.wordOffset = 0) (unpacked : member.packed = none)
    (persistent : fieldIsTransient fields name = false)
    (keyEval : evalExpr oracle fields state key = some resolvedKey)
    (valueEval : evalExpr oracle fields state value = some resolvedValue) :
    execStmt oracle fields state (.setStructMember name key memberName value) =
      .continue { state with
        world := state.world.writeSlot (wordNormalize (oracle.mappingSlot base resolvedKey))
          (Verity.Core.Uint256.ofNat resolvedValue) } := by
  rcases member with ⟨memberName, ty, wordOffset, packed⟩
  dsimp only at offset unpacked
  subst wordOffset
  subst packed
  simp only [execStmt, slots, layout, keyEval, valueEval, found]
  rw [singleton_write oracle fields name state.world base resolvedKey resolvedValue persistent]

end Compiler.Proofs.IRGeneration.ImportedMappingEffect
