import Compiler.SolidityImport.TransactionAccess

namespace SolidityImportSmoke.Transactions
open Compiler.CompilationModel Compiler.CompilationModel.Denote
open Compiler.CompilationModel.SolidityImport.Transactions

-- Neither hash oracle is reached by this scalar-only frame regression.
private def oracle : DenoteOracle := ⟨fun _ _ => 0, fun _ _ _ => 0⟩
private def fields : List Field :=
  [{ name := "stored", ty := .uint256 },
   { name := "scratch", ty := .uint256, isTransient := true }]

#eval show IO Unit from do
  let first ← IO.ofExcept (executeBody oracle fields Verity.defaultState []
    [.setStorage "stored" (.literal 7), .setStorage "scratch" (.literal 11),
     .returnValues [.storage "stored", .storage "scratch"]])
  unless first.success && first.data == (wordBytes 7 ++ wordBytes 11) do
    throw (IO.userError "first Denote transaction observation differs")
  let second ← IO.ofExcept (executeBody oracle fields first.world []
    [.returnValues [.storage "stored", .storage "scratch"]])
  unless second.success && second.data == (wordBytes 7 ++ wordBytes 0) do
    throw (IO.userError "persistent/transient transaction boundary differs")
  let failed ← IO.ofExcept (executeBody oracle fields second.world []
    [.setStorage "stored" (.literal 99), .panic .arithmeticOverflow])
  unless !failed.success && failed.data == panicBytes 0x11 &&
      (failed.world.readSlot 0).val == 7 do
    throw (IO.userError "reverted Denote write or exact payload differs")
  let third ← IO.ofExcept (executeBody oracle fields failed.world []
    [.returnValues [.storage "stored"]])
  unless third.success && third.data == wordBytes 7 do
    throw (IO.userError "sequence did not resume from rolled-back state")
  match executeBody oracle fields third.world [] [.setStorage "missing" (.literal 1)] with
  | .error _ => pure ()
  | .ok _ => throw (IO.userError "unsupported Denote failure became a contract revert")
  let traced ← IO.ofExcept (traceStraightLine oracle fields
    { world := beginTransaction third.world, bindings := [] }
    [.setStorage "stored" (.storage "scratch"), .panic .arithmeticOverflow,
     .setStorage "scratch" (.literal 123)])
  unless traced.touched == [.transient 1, .slot 0] do
    throw (IO.userError "reverted accesses were lost or unreachable writes were observed")
  let rolledBack ← IO.ofExcept (finishFrame (beginTransaction third.world) traced.outcome)
  unless !rolledBack.success && (rolledBack.world.readSlot 0).val == 7 do
    throw (IO.userError "access instrumentation changed rollback")
  match traceStraightLine oracle fields { world := third.world, bindings := [] }
      [.emit "UnknownEvent" []] with
  | .error _ => pure ()
  | .ok _ => throw (IO.userError "unsupported access observation was silently accepted")
  let combined ← IO.ofExcept (executeTracedBody oracle fields third.world []
    [.setStorage "stored" (.literal 55), .panic .arithmeticOverflow])
  unless combined.touched == [.slot 0] && !combined.frame.success &&
      combined.frame.data == panicBytes 0x11 && (combined.frame.world.readSlot 0).val == 7 do
    throw (IO.userError "combined Denote frame lost rollback, payload or accesses")
  IO.println "Denote transaction persistence, transient reset, exact panic, rollback and access traces passed"
end SolidityImportSmoke.Transactions
