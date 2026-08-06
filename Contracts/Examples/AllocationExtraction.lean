import Verity.Core.Model.AllocationExtraction

namespace Contracts.Examples.AllocationExtraction

open Compiler.CompilationModel
open Verity.Core.Model.AllocationExtraction

def aField : Field := { name := "a", ty := .uint256, slot := some 3 }
def bField : Field := { name := "b", ty := .uint256, slot := some 7 }

def exampleSpec : CompilationModel :=
  { name := "AllocationExample"
    fields := [aField, bField]
    constructor := none
    functions := [] }

/-- Read slot A and conditionally write slot B. -/
def readAWriteB : FunctionSpec :=
  { name := "readAWriteB"
    params := []
    returnType := none
    body := [
      .ite (.gt (.storage "a") (.literal 0))
        [.setStorage "b" (.literal 1)] []] }

def readAEntry : AllocEntry :=
  { contract := 0, slot := 3, kind := .read, constraint := fun _ => True }

def writeBEntry : AllocEntry :=
  { contract := 0, slot := 7, kind := .write, constraint := fun _ => True }

example : (extractAllocation exampleSpec readAWriteB).slots.map
    (fun entry => (entry.slot, entry.kind)) = [(3, .read), (7, .write)] := by
  have ha : findFieldWithResolvedSlot [aField, bField] "a" = some (aField, 3) := by
    rfl
  have hb : findFieldWithResolvedSlot [aField, bField] "b" = some (bField, 7) := by
    rfl
  simp [extractAllocation, storageAccesses, storageAccessesBody,
    shallowConditionalAccesses?, directStorageAccesses, storageReads,
    shallowExprStorageReads?, exprStorageRoot?, Expr.children, Stmt.childLists,
    Stmt.directMetadata, resolveAccess, ha, hb, exampleSpec, readAWriteB, contractId]

example : (extractAllocation exampleSpec readAWriteB).returns = [] := by
  decide

end Contracts.Examples.AllocationExtraction
