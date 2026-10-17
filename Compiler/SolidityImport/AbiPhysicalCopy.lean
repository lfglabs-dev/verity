import Compiler.SolidityImport.AbiPhysicalMemory
import Compiler.SolidityImport.AbiMemoryGrid
import Verity.Core.Model.ByteMemoryInverse

namespace Compiler.CompilationModel.Denote
open Compiler.CompilationModel.PhysicalMemory
open Compiler.CompilationModel.DenoteMemory

/-- Actual world written by the emitted aligned read/modify/store insertion. -/
def abiInsertByteWorld (world : Verity.ContractState) (address byte : Nat) :
    Verity.ContractState :=
  world.writePhysicalMemoryValue (address / 32 * 32)
    (Verity.Core.Uint256.ofNat (SolidityImport.AbiByteLanes.insert
      (world.memory (address / 32 * 32)).val byte (31 - address % 32)))

/-- Only aligned grid projections match the mathematical single-cell update.
Overlapping, unaligned word windows are retained in the actual physical world. -/
theorem abiInsertByteWorld_grid (world : Verity.ContractState) (address byte cell : Nat)
    (coherent : Coherent world) (aligned : cell % 32 = 0) :
    (abiInsertByteWorld world address byte).memory cell =
      abiInsertByte world.memory address byte cell := by
  by_cases same : cell = address / 32 * 32
  · subst cell
    simp only [abiInsertByteWorld, abiInsertByte, if_pos rfl]
    exact writePhysicalMemoryValue_at world (address / 32 * 32) _
  · have gridAligned : (address / 32 * 32) % 32 = 0 := by omega
    have disjoint : cell + 32 ≤ address / 32 * 32 ∨ address / 32 * 32 + 32 ≤ cell := by
      omega
    have frame := writePhysicalMemoryWord_outside world (address / 32 * 32)
      (valueWord (Verity.Core.Uint256.ofNat (SolidityImport.AbiByteLanes.insert
        (world.memory (address / 32 * 32)).val byte (31 - address % 32)))) cell coherent disjoint
    change (world.writePhysicalMemoryWord _ _).memory cell = _
    rw [frame]
    simp only [abiInsertByte, if_neg same]

/-- All grid byte observations follow from the geometric word frame. -/
theorem abiInsertByteWorld_byte_grid (world : Verity.ContractState) (address byte query : Nat)
    (coherent : Coherent world) :
    abiMemoryByte (abiInsertByteWorld world address byte).memory query =
      abiMemoryByte (abiInsertByte world.memory address byte) query := by
  unfold abiMemoryByte
  rw [abiInsertByteWorld_grid world address byte (query / 32 * 32) coherent (by omega)]

/-- The mathematical byte observation is exactly the real byte carrier for
coherent worlds, rather than a replacement for it. -/
theorem abiMemoryByte_physical (world : Verity.ContractState) (address : Nat)
    (coherent : Coherent world) :
    abiMemoryByte world.memory address = (world.physicalByte address).val :=
  (physicalByte_word_grid_value world coherent address).symm

/-- Actual physical byte result of the insertion, including its full outside
byte frame through the existing mathematical insertion laws. -/
theorem abiInsertByteWorld_physical_byte (world : Verity.ContractState) (address byte query : Nat)
    (coherent : Coherent world) :
    ((abiInsertByteWorld world address byte).physicalByte query).val =
      abiMemoryByte (abiInsertByte world.memory address byte) query := by
  rw [← abiMemoryByte_physical (abiInsertByteWorld world address byte) query
    (writePhysicalMemoryValue_coherent world _ _)]
  exact abiInsertByteWorld_byte_grid world address byte query coherent

/-- Whole actual store poststate, with no coherence or zero-byte assumption. -/
theorem execStmt_mstore_abiInsertByte_physical (oracle : DenoteOracle) (fields : List Field)
    (state : DenoteState) (offset value : Expr) (address byte : Nat)
    (resolvedOffset : evalExpr oracle fields state offset = some (address / 32 * 32))
    (resolvedValue : evalExpr oracle fields state value = some
      (SolidityImport.AbiByteLanes.insert (state.world.memory (address / 32 * 32)).val
        byte (31 - address % 32))) :
    execStmt oracle fields state (.mstore offset value) =
      .continue { state with world := abiInsertByteWorld state.world address byte } :=
  execStmt_mstore_physical oracle fields state offset value (address / 32 * 32) _
    resolvedOffset resolvedValue

end Compiler.CompilationModel.Denote
