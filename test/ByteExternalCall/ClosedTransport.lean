import Compiler.Modules.SolidityStaticCall

open Compiler.ECM Compiler.Yul

private def module := SolidityStaticCall.uint256Module "result" 0xa035b1fe 0
private def arguments : List YulExpr := [.lit 23]

-- The closure is deliberately different. Closed transports compile from the
-- descriptor, so neither quotation nor compiler behavior depends on it.
example : ({ module with compile := fun _ _ => .ok [] } : ExternalCallModule).compileCanonical
    {} arguments = module.compileCanonical {} arguments := rfl

-- Contradictory metadata cannot gain the semantics of a readonly transport.
example : ({ module with writesState := true } : ExternalCallModule).compileCanonical
    {} arguments = .error "closed Solidity staticcall transport metadata differs" := rfl

example : ({ module with resultVars := [] } : ExternalCallModule).compileCanonical
    {} arguments = .error "closed Solidity staticcall transport metadata differs" := rfl

example : ({ module with numArgs := 2 } : ExternalCallModule).compileCanonical
    {} arguments = .error "closed Solidity staticcall transport metadata differs" := rfl
