import Compiler.SolidityImport.Import
import Compiler.Proofs.IRGeneration.ImportedPrefixFrames
import Compiler.Proofs.IRGeneration.ImportedMappingEffect
import Compiler.Proofs.IRGeneration.ImportedAbiOperands

namespace Contracts.SolidityImportSmoke.ImportedCreationPrefixFrames
open Compiler.CompilationModel
solidity_import imported from "Contracts/SolidityImportSmoke" entry "ImportedCreationPrefix.sol"
  using { evmVersion := "osaka", viaIR := true, optimizerRuns := some 466, bytecodeHash := "none" }
  contract SourcePrefix
  function deploy(Market, uint256, uint256)
end Contracts.SolidityImportSmoke.ImportedCreationPrefixFrames

namespace Contracts.SolidityImportSmoke.ImportedCreationPrefixFrames
open Compiler.CompilationModel Compiler.Proofs.IRGeneration.ImportedPrefixFrames

def mappingWrite : Stmt → Bool
  | .setStructMember "values" _ "__solidity_value" _ => true
  | _ => false

def prefixCertificate : List FunctionSpec → Bool
  | [fn] =>
    let body := fn.body.dropLast
    let index := body.findIdx mappingWrite
    safeList (body.take index) &&
      (body[index]?.map mappingWrite).getD false &&
      safeList (body.drop (index + 1)) &&
      (match fn.body.getLast? with | some (.returnBytes _) => true | _ => false)
  | _ => false

/-- Only AST classification is reduced by the kernel; no interpreter/memory execution. -/
theorem actual_imported_prefix_certificate : prefixCertificate imported.model.functions = true := by
  decide

/-- Every actual execution of either imported memory/control segment preserves
all nonmemory world fields, for arbitrary inputs, bindings and oracle. -/
theorem actual_imported_prefix_frames (oracle : Denote.DenoteOracle) (fields : List Field)
    (fn : FunctionSpec) (shape : imported.model.functions = [fn]) (state : Denote.DenoteState) :
    let body := fn.body.dropLast
    let index := body.findIdx mappingWrite
    preserves state (Denote.execStmtList oracle fields state (body.take index)) ∧
      preserves state (Denote.execStmtList oracle fields state (body.drop (index + 1))) := by
  have certified := actual_imported_prefix_certificate
  rw [shape] at certified
  simp only [prefixCertificate, Bool.and_eq_true] at certified
  exact ⟨list_frame oracle fields _ certified.1.1.1 state,
    list_frame oracle fields _ certified.1.2 state⟩

/-- Every successful actual imported prefix factors through its unique mapping
write; the ABI/initcode segments preserve every nonmemory world field. -/
theorem actual_prefix_isolate (oracle : Denote.DenoteOracle) (fields : List Field)
    (fn : FunctionSpec) (shape : imported.model.functions = [fn])
    (initial final : Denote.DenoteState)
    (executed : Denote.execStmtList oracle fields initial fn.body.dropLast = .continue final) :
    let body := fn.body.dropLast
    let index := body.findIdx mappingWrite
    ∃ pre post effect, body[index]? = some effect ∧
      Denote.execStmtList oracle fields initial (body.take index) = .continue pre ∧
      Denote.execStmt oracle fields pre effect = .continue post ∧
      Compiler.Proofs.IRGeneration.CreationMemoryFrames.eraseMemory pre.world =
        Compiler.Proofs.IRGeneration.CreationMemoryFrames.eraseMemory initial.world ∧
      Compiler.Proofs.IRGeneration.CreationMemoryFrames.eraseMemory final.world =
        Compiler.Proofs.IRGeneration.CreationMemoryFrames.eraseMemory post.world := by
  have certified := actual_imported_prefix_certificate
  rw [shape] at certified
  simp only [prefixCertificate, Bool.and_eq_true] at certified
  have present := certified.1.1.2
  have bound : fn.body.dropLast.findIdx mappingWrite < fn.body.dropLast.length := by
    by_contra absent
    have missing := List.getElem?_eq_none (Nat.le_of_not_gt absent)
    rw [missing] at present
    cases present
  obtain ⟨pre, post, ranBefore, ranWrite, beforeFrame, afterFrame⟩ :=
    isolate_index oracle fields fn.body.dropLast _ bound initial final
      certified.1.1.1 certified.1.2 executed
  exact ⟨pre, post, fn.body.dropLast[fn.body.dropLast.findIdx mappingWrite],
    List.getElem?_eq_getElem bound, ranBefore, ranWrite, beforeFrame, afterFrame⟩

/-- Complete effect of the exact mapping instruction emitted by this importer.
The local values remain explicit; linking them to ABI words is a separate step. -/
theorem actual_mapping_instruction (oracle : Denote.DenoteOracle) (state : Denote.DenoteState) :
    Denote.execStmt oracle (Denote.effectiveFields imported.model) state
      (.setStructMember "values" (.localVar "_verity_slice_tmp_1") "__solidity_value"
        (.localVar "_verity_slice_tmp_2")) =
      .continue { state with
        world := state.world.writeSlot
          (Denote.wordNormalize (oracle.mappingSlot 0 (Denote.lookupValue state.bindings "_verity_slice_tmp_1")))
          (Verity.Core.Uint256.ofNat (Denote.lookupValue state.bindings "_verity_slice_tmp_2")) } := by
  exact Compiler.Proofs.IRGeneration.ImportedMappingEffect.resolved_member_write
    oracle (Denote.effectiveFields imported.model) state "values" "__solidity_value"
    (.localVar "_verity_slice_tmp_1") (.localVar "_verity_slice_tmp_2") 0 _ _
    [{ name := "__solidity_value", wordOffset := 0 }]
    { name := "__solidity_value", wordOffset := 0 }
    (by rfl) (by rfl) (by rfl) (by rfl) (by rfl) (by rfl) (by rfl) (by rfl)

/-- The instruction just analyzed is the actual node at the certified index. -/
theorem actual_mapping_node :
    (imported.model.functions.head?.map fun fn => fn.body.dropLast[38]?).getD none =
      some (.setStructMember "values" (.localVar "_verity_slice_tmp_1") "__solidity_value"
        (.localVar "_verity_slice_tmp_2")) := by
  rfl

/-- Complete nonmemory effect of every successful actual imported prefix.
Only the two actual local operands at the isolated write remain to link to ABI. -/
theorem actual_prefix_effect (oracle : Denote.DenoteOracle)
    (fn : FunctionSpec) (shape : imported.model.functions = [fn])
    (initial final : Denote.DenoteState)
    (executed : Denote.execStmtList oracle (Denote.effectiveFields imported.model)
      initial fn.body.dropLast = .continue final) :
    ∃ pre, Denote.execStmtList oracle (Denote.effectiveFields imported.model)
        initial (fn.body.dropLast.take 38) = .continue pre ∧
      Compiler.Proofs.IRGeneration.CreationMemoryFrames.eraseMemory final.world =
        (Compiler.Proofs.IRGeneration.CreationMemoryFrames.eraseMemory initial.world).writeSlot
          (Denote.wordNormalize (oracle.mappingSlot 0 (Denote.lookupValue pre.bindings "_verity_slice_tmp_1")))
          (Verity.Core.Uint256.ofNat (Denote.lookupValue pre.bindings "_verity_slice_tmp_2")) := by
  have actualIndex : (imported.model.functions.head?.map fun f => f.body.dropLast.findIdx mappingWrite) = some 38 := by
    rfl
  rw [shape] at actualIndex
  have index : fn.body.dropLast.findIdx mappingWrite = 38 := Option.some.inj actualIndex
  have actualNode := actual_mapping_node
  rw [shape] at actualNode
  simp only [List.head?_cons, Option.map_some, Option.getD_some] at actualNode
  obtain ⟨pre, post, effect, node, ranBefore, ranWrite, beforeFrame, afterFrame⟩ :=
    actual_prefix_isolate oracle (Denote.effectiveFields imported.model) fn shape initial final executed
  rw [index] at node ranBefore
  have effectEq := Option.some.inj (node.symm.trans actualNode)
  subst effect
  have postEq := Denote.StmtOutcome.continue.inj
    (ranWrite.symm.trans (actual_mapping_instruction oracle pre))
  rw [postEq] at afterFrame
  refine ⟨pre, ranBefore, ?_⟩
  simpa only [Compiler.Proofs.IRGeneration.ImportedMappingEffect.erase_write, beforeFrame] using afterFrame

/-- The two loads are the actual suffix of the imported pre-write segment. -/
theorem actual_operand_suffix :
    (imported.model.functions.head?.map fun fn => fn.body.dropLast.take 38) =
      (imported.model.functions.head?.map fun fn => fn.body.dropLast.take 36 ++
        Compiler.Proofs.IRGeneration.ImportedAbiOperands.loads) := by
  rfl

theorem actual_abi_setup_certificate :
    (imported.model.functions.head?.map fun fn => safeList (fn.body.dropLast.take 36)) = some true := by
  decide

/-- Actual prefix execution supplies ABI operands, not assumed local bindings. -/
theorem actual_prefix_operands (oracle : Denote.DenoteOracle) (fields : List Field)
    (fn : FunctionSpec) (shape : imported.model.functions = [fn])
    (initial pre : Denote.DenoteState)
    (executed : Denote.execStmtList oracle fields initial (fn.body.dropLast.take 38) = .continue pre) :
    Denote.lookupValue pre.bindings "_verity_slice_tmp_1" =
        initial.world.calldata.getD 1 0 % Compiler.Constants.evmModulus ∧
      Denote.lookupValue pre.bindings "_verity_slice_tmp_2" =
        initial.world.calldata.getD 2 0 % Compiler.Constants.evmModulus := by
  have suffix := actual_operand_suffix
  rw [shape] at suffix
  have split := Option.some.inj suffix
  dsimp only at split
  rw [split] at executed
  obtain ⟨mid, ranSetup, ranLoads⟩ := SolidityImport.split_prefix_continue
    oracle fields initial pre (fn.body.dropLast.take 36)
      Compiler.Proofs.IRGeneration.ImportedAbiOperands.loads executed
  rw [Compiler.Proofs.IRGeneration.ImportedAbiOperands.execute_loads] at ranLoads
  have preEq := Denote.StmtOutcome.continue.inj ranLoads.symm
  have certified := actual_abi_setup_certificate
  rw [shape] at certified
  have frame := list_frame oracle fields _ (Option.some.inj certified) initial
  have same : Compiler.Proofs.IRGeneration.CreationMemoryFrames.eraseMemory mid.world =
      Compiler.Proofs.IRGeneration.CreationMemoryFrames.eraseMemory initial.world := by
    simpa only [preserves, ranSetup] using frame
  have projected := congrArg (fun w : Verity.ContractState => w.calldata) same
  have calldata : mid.world.calldata = initial.world.calldata := by
    simpa only [Compiler.Proofs.IRGeneration.CreationMemoryFrames.eraseMemory,
      Verity.ContractState.installPhysicalMemory] using projected
  rw [preEq, Compiler.Proofs.IRGeneration.ImportedAbiOperands.loaded_key,
    Compiler.Proofs.IRGeneration.ImportedAbiOperands.loaded_value, calldata]
  exact ⟨rfl, rfl⟩

/-- Exact complete nonmemory effect in terms of original ABI words. -/
theorem actual_prefix_abi_effect (oracle : Denote.DenoteOracle)
    (fn : FunctionSpec) (shape : imported.model.functions = [fn])
    (initial final : Denote.DenoteState)
    (executed : Denote.execStmtList oracle (Denote.effectiveFields imported.model)
      initial fn.body.dropLast = .continue final) :
    Compiler.Proofs.IRGeneration.CreationMemoryFrames.eraseMemory final.world =
      (Compiler.Proofs.IRGeneration.CreationMemoryFrames.eraseMemory initial.world).writeSlot
        (Denote.wordNormalize (oracle.mappingSlot 0
          (initial.world.calldata.getD 1 0 % Compiler.Constants.evmModulus)))
        (Verity.Core.Uint256.ofNat (initial.world.calldata.getD 2 0 % Compiler.Constants.evmModulus)) := by
  obtain ⟨pre, ranBefore, effect⟩ := actual_prefix_effect oracle fn shape initial final executed
  have operands := actual_prefix_operands oracle (Denote.effectiveFields imported.model)
    fn shape initial pre ranBefore
  rwa [operands.1, operands.2] at effect

end Contracts.SolidityImportSmoke.ImportedCreationPrefixFrames
