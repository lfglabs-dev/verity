import Compiler.Proofs.IRGeneration.DispatchGeneric
import Compiler.Proofs.AbiEncoding

/-!
# Dispatcher correctness at a `bytes` external parameter

`interpretContract_correct_of_functions_generic_external` is generic in the
parameter shape, but it takes `hbindTotal` — "arity suffices for the external
ABI binder to succeed" — as a hypothesis.  For scalar parameters that is a
theorem about arity alone.  For `bytes` it is **false** on arbitrary calldata:
a malformed head offset or a truncated tail makes `bindExternalParam` return
`none`, so instantiating the generic theorem at a `bytes` parameter without
discharging `hbindTotal` would be vacuous.

This module discharges it from the ABI encoder: on calldata that really is
`abiEncodeArgs` of a well-formed `bytes` argument, the binder succeeds and
recovers the true offset, byte length and remaining tail size
(`Compiler.Proofs.AbiEncoding.bindExternalParams_bytes_of_abiEncodeArgs`), and
feeds that into the generic dispatcher theorem.
-/

namespace Compiler.Proofs.IRGeneration

open Compiler
open Compiler.CompilationModel
open Compiler.Proofs.AbiEncoding
open Dispatch

namespace BytesParamDispatch

/-- The external ABI binder is total on a single `bytes` entrypoint parameter
when the transaction arguments are a real ABI encoding.  This is exactly the
`hbindTotal` obligation of the generic dispatcher theorem. -/
theorem bindExternalParams_total_of_bytes_calldata
    (model : CompilationModel) (tx : IRTransaction)
    (name : String) (value : AbiBytes)
    (hwf : value.WellFormed)
    (hargs : tx.args = abiEncodeArgs [AbiArg.bytes value])
    (hsize : 4 + 32 * tx.args.length < Compiler.Constants.evmModulus)
    (hparams : ∀ fn ∈ selectorDispatchedFunctions model,
      fn.params = [{ name := name, ty := ParamType.bytes }]) :
    ∀ fn ∈ selectorDispatchedFunctions model,
      fn.params.length ≤ tx.args.length →
      ∃ bindings,
        SourceSemantics.bindExternalParams tx.functionSelector fn.params tx.args =
          some bindings := by
  intro fn hfn _
  have hbind :
      SourceSemantics.bindExternalParams tx.functionSelector fn.params tx.args =
        some
          [ (s!"{name}_offset", 32)
          , (s!"{name}_abs_offset", 36)
          , (s!"{name}_length", value.byteLength)
          , (s!"{name}_tail_head_end", 68)
          , (s!"{name}_tail_remaining", 32 * value.dataWords.length)
          , (s!"{name}_data_offset", 68) ] := by
    rw [hparams fn hfn, hargs]
    exact bindExternalParams_bytes_of_abiEncodeArgs tx.functionSelector name value hwf
      (by rw [← hargs]; exact hsize)
  exact ⟨_, hbind⟩

/-- Whole-contract dispatcher correctness for entrypoints taking a `bytes`
parameter.  `hbindTotal` is gone: it is discharged from the ABI encoding, so
the statement is non-vacuous at `bytes`. -/
theorem interpretContract_correct_of_functions_bytes_param
    (P : FunctionSpec → Nat → IRFunction → Prop)
    (model : CompilationModel) (selectors : List Nat)
    (irFns : List IRFunction) (tx : IRTransaction)
    (initialWorld : Verity.ContractState)
    (name : String) (value : AbiBytes)
    (hwf : value.WellFormed)
    (hargs : tx.args = abiEncodeArgs [AbiArg.bytes value])
    (hsize : 4 + 32 * tx.args.length < Compiler.Constants.evmModulus)
    (hparams : ∀ fn ∈ selectorDispatchedFunctions model,
      fn.params = [{ name := name, ty := ParamType.bytes }])
    (hmeta : ∀ fn sel irFn, P fn sel irFn →
      irFn.params = fn.params.map Param.toIRParam ∧
        irFn.selector = sel ∧ irFn.payable = fn.isPayable)
    (hcompiled : List.Forall₂ (fun entry irFn => P entry.1 entry.2 irFn)
      (SourceSemantics.selectorFunctionPairs model selectors) irFns)
    (hfunction :
      ∀ fn sel irFn bindings,
        fn ∈ selectorDispatchedFunctions model →
        P fn sel irFn →
        SourceSemantics.bindExternalParams tx.functionSelector fn.params tx.args =
          some bindings →
        FunctionBody.sourceResultMatchesIRResult
          (SourceSemantics.interpretFunction model fn tx initialWorld)
          (execIRFunction irFn tx.args
            (FunctionBody.initialIRStateForTx model tx initialWorld))) :
    FunctionBody.sourceResultMatchesIRResult
      (SourceSemantics.interpretContract model selectors tx initialWorld)
      (interpretIR (runtimeContractOfFunctions model.name irFns) tx
        (FunctionBody.initialIRStateForTx model tx initialWorld)) :=
  interpretContract_correct_of_functions_generic_external P model selectors irFns tx
    initialWorld hmeta hcompiled
    (bindExternalParams_total_of_bytes_calldata model tx name value hwf hargs hsize hparams)
    hfunction

end BytesParamDispatch

end Compiler.Proofs.IRGeneration
