import Verity.Core.Model.AllocationExtraction
import Compiler.Proofs.Storage.StructArrayStorage

/-!
# Top-up allocation and two-word storage bounds

This module specializes allocation extraction to the two canonical words rooted
at `TopUpGateway.GATEWAY_STORAGE_POSITION` in the pinned Solidity source.  It
also records the arithmetic and packed-word obligations needed by the deposit
flow without extending the trusted base.
-/

namespace Verity.Core.Model.TopupAllocation

open Compiler.CompilationModel
open Compiler.Proofs.Storage
open Verity.Core.Model.AllocationExtraction

/-- `keccak256(abi.encode(uint256(keccak256("lido.TopUpGateway.storage")) - 1))
    & ~bytes32(uint256(0xff))`, as pinned by `TopUpGateway.sol`. -/
def gatewayStoragePosition : Nat :=
  0x22e512057841e2bc1e6d80030c8bb8b4935377af2e64ba9bf8e6a3e88fb32200

def gatewayWord0Slot : ByteArray := slotPointer gatewayStoragePosition

def gatewayWord1Slot : ByteArray := slotPointer (gatewayStoragePosition + 1)

/-- The two words of the TopUpGateway namespaced-storage footprint. -/
inductive GatewayWord where
  | word0
  | word1
  deriving Repr, DecidableEq

/-- Classify a canonical allocation entry when it belongs to the gateway's
    two-word namespace. -/
def classifyGatewayWord (entry : AllocEntry) : Option GatewayWord :=
  if entry.slot = gatewayStoragePosition then some .word0
  else if entry.slot = gatewayStoragePosition + 1 then some .word1
  else none

/-- Typed view of the allocation extracted for the TopUpGateway deposit flow.
    `raw` retains the complete extractor result; `namespaceSlots` contains only
    the two words owned by this namespace, tagged by word. -/
structure GatewayAllocation where
  raw : Allocation
  namespaceSlots : List (AllocEntry × GatewayWord)

/-- Specialize the canonical allocation extractor to TopUpGateway's two-word
    deposit namespace. -/
def extractGatewayAllocation (spec : CompilationModel) (fn : FunctionSpec) :
    GatewayAllocation :=
  let allocation := extractAllocation spec fn
  { raw := allocation
    namespaceSlots := allocation.slots.filterMap fun entry =>
      (classifyGatewayWord entry).map (entry, ·) }

theorem extractGatewayAllocation_raw
    (spec : CompilationModel) (fn : FunctionSpec) :
    (extractGatewayAllocation spec fn).raw = extractAllocation spec fn := by
  rfl

/-- Every typed namespace entry comes from the canonical extraction result. -/
theorem extractGatewayAllocation_namespace_mem_raw
    (spec : CompilationModel) (fn : FunctionSpec)
    (entry : AllocEntry) (word : GatewayWord)
    (hmem : (entry, word) ∈ (extractGatewayAllocation spec fn).namespaceSlots) :
    entry ∈ (extractAllocation spec fn).slots := by
  simp only [extractGatewayAllocation, List.mem_filterMap] at hmem
  obtain ⟨source, hsource, hclassified⟩ := hmem
  rw [Option.map_eq_some_iff] at hclassified
  obtain ⟨classified, _, hpair⟩ := hclassified
  injection hpair with hentry _
  subst entry
  exact hsource

/-- The two `uint128`-bounded operands used by the deposit accumulator cannot
    wrap a 256-bit EVM word. -/
theorem depositAmount_add_noWrap
    (amount accumulated : Nat)
    (hamount : amount < 2 ^ 128)
    (haccumulated : accumulated < 2 ^ 128) :
    amount + accumulated < 2 ^ 256 := by
  have hhalf : amount + accumulated < 2 ^ 129 := by omega
  have hpowers : (2 : Nat) ^ 129 ≤ 2 ^ 256 := by norm_num
  omega

/-! ## Packed two-word preservation

The active flag is the one-bit packed observation in word 0.  Word 1 contains
the 128-bit deposit counter followed by the 128-bit amount accumulator.  The
invariant intentionally mentions the active flag and counter; accumulator
updates are free provided the low counter field remains correct.
-/

def activeFlag (storage : SolidityStorage) (contract : ContractId) : Nat :=
  (yulReadPackedWord (storage contract gatewayWord0Slot) 0 1).toNat

def depositCounter (storage : SolidityStorage) (contract : ContractId) : Nat :=
  (yulReadPackedWord (storage contract gatewayWord1Slot) 0 128).toNat

def amountAccumulator (storage : SolidityStorage) (contract : ContractId) : Nat :=
  (yulReadPackedWord (storage contract gatewayWord1Slot) 128 128).toNat

/-- Active-flag consistency and deposit-counter correctness across both words. -/
def GatewayStorageInvariant (storage : SolidityStorage) (contract : ContractId)
    (expectedActive expectedCounter : Nat) : Prop :=
  activeFlag storage contract = expectedActive ∧
    depositCounter storage contract = expectedCounter

/-- A single canonical write to either gateway word preserves the two-word
    invariant when the field in the word being replaced has the expected value.
    This is the precise preservation condition required of a packed
    read-modify-write; the neighbouring word is protected by slot separation. -/
theorem applyStorageWrite_preserves_gatewayInvariant
    (storage : SolidityStorage) (write : StorageWrite) (contract : ContractId)
    (expectedActive expectedCounter : Nat)
    (hinvariant : GatewayStorageInvariant storage contract expectedActive expectedCounter)
    (hcontract : write.contract = contract)
    (htarget : write.slot = gatewayWord0Slot ∨ write.slot = gatewayWord1Slot)
    (hactive : write.slot = gatewayWord0Slot →
      (yulReadPackedWord write.value 0 1).toNat = expectedActive)
    (hcounter : write.slot = gatewayWord1Slot →
      (yulReadPackedWord write.value 0 128).toNat = expectedCounter)
    (hdistinct : gatewayWord0Slot ≠ gatewayWord1Slot) :
    GatewayStorageInvariant (applyStorageWrite write storage) contract
      expectedActive expectedCounter := by
  rcases hinvariant with ⟨holdActive, holdCounter⟩
  rcases htarget with hword0 | hword1
  · constructor
    · simp [activeFlag, applyStorageWrite, hcontract, hword0,
        hactive hword0]
    · have hne : gatewayWord1Slot ≠ write.slot := by
        intro heq
        apply hdistinct
        exact hword0.symm.trans heq.symm
      simpa [GatewayStorageInvariant, depositCounter, applyStorageWrite, hcontract, hne]
        using holdCounter
  · constructor
    · have hne : gatewayWord0Slot ≠ write.slot := by
        intro heq
        apply hdistinct
        exact heq.trans hword1
      simpa [GatewayStorageInvariant, activeFlag, applyStorageWrite, hcontract, hne]
        using holdActive
    · simp [depositCounter, applyStorageWrite, hcontract, hword1,
        hcounter hword1]

end Verity.Core.Model.TopupAllocation
