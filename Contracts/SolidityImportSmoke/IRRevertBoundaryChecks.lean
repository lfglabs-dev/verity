import Compiler.Proofs.IRGeneration.FunctionBody.Stmt

namespace SolidityImportSmoke.IRRevertBoundaryChecks
open Compiler.Proofs.IRGeneration Compiler.Yul

def probe (offset size fuel : Nat) : Option (List UInt8) :=
  let entry := (IRState.initial 0).writePhysicalMemoryValue 0 0x0102030405
  let result := execIRStmt fuel entry
    (.exprStmt (.call "revert" [.lit offset, .lit size]))
  (FunctionBody.irResultOfExecResult entry result).revertData

def runChecks : IO Unit := do
  unless probe 27 5 1 == some [1, 2, 3, 4, 5] do
    throw (IO.userError "opcode/public result lost nonempty REVERT bytes")
  unless probe 30 5 1 == some [4, 5, 0, 0, 0] do
    throw (IO.userError "opcode/public result changed REVERT offset or zero expansion")
  unless probe 255 0 1 == some [] do
    throw (IO.userError "executed zero-size REVERT lost its observation")
  unless probe 27 5 0 == none do
    throw (IO.userError "fuel exhaustion fabricated observed REVERT bytes")

end SolidityImportSmoke.IRRevertBoundaryChecks

def main : IO Unit := SolidityImportSmoke.IRRevertBoundaryChecks.runChecks
