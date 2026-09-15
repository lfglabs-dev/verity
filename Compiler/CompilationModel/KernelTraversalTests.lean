import Compiler.CompilationModel.InternalArgs
open Compiler.CompilationModel

-- These are deliberately kernel decisions; native execution cannot validate
-- whether the compiler traversal equations are available to the kernel.
example : staticParamBindingNames "p" (.tuple [.uint256, .fixedArray .address 2]) =
    ["p_0", "p_1_0", "p_1_1"] := by decide +kernel
example : paramLocalHeadWords (.tuple [.bytes, .fixedArray .uint256 3]) = 4 := by
  decide +kernel
example : paramParentHeadWords (.tuple [.bytes, .fixedArray .uint256 3]) = 1 := by
  decide +kernel
example : Stmt.controlFlowList [.require (.literal 1) "ok", .return (.literal 1), .stop] =
    ControlFlowSummary.seq .mayReverting .returns := by
  simp [Stmt.controlFlowList, Stmt.controlFlow, ControlFlowSummary.seq,
    ControlFlowSummary.mayReverting, ControlFlowSummary.returns,
    ControlFlowSummary.stops, ControlFlowSummary.fallsThrough]
example : Stmt.foldList
    (fun acc stmt _ => match stmt with | .letVar name _ => acc ++ [name] | _ => acc)
    [] [.letVar "first" (.literal 0),
        .ite (.literal 1) [.letVar "then" (.literal 0)] [.letVar "else" (.literal 0)],
        .letVar "last" (.literal 0)] = ["first", "then", "else", "last"] := by
  decide +kernel
