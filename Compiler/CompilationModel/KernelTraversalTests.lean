import Compiler.CompilationModel.InternalArgs
import Compiler.CompilationModel.TrustSurface
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

-- Preserve traversal order, nested expression mechanics, deduplication, and
-- the exclusion of bodies that already carry an explicit unsafe reason.
example : collectUnguardedUnsafeBoundaryMechanicsFromStmts
    [.letVar "x" (.mload (.calldataload (.literal 0))),
     .ite (.literal 1)
       [.mstore (.literal 0) (.mload (.literal 32))]
       [.unsafeBlock "documented elsewhere" [.mstore (.literal 0) (.literal 1)]],
     .forEach "i" (.literal 2) [.letVar "y" (.extcodesize (.literal 1))]] =
    ["mload", "calldataload", "mstore", "extcodesize"] := by
  decide +kernel

example : collectUnguardedUnsafeBoundaryMechanicsFromStmts
    [.letVar "x" (.add (.literal 1) (.literal 2)),
     .return (.localVar "x")] = [] := by
  decide +kernel
