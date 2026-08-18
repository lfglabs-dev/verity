import Compiler.Proofs.IRGeneration.DispatchGeneric
import Compiler.Proofs.AbiEncoding

/-!
# Dispatcher correctness at a `string` external parameter

The `bytes` module next door explains why `hbindTotal` cannot be left as a
hypothesis for a dynamic parameter: on arbitrary calldata the external binder
returns `none`, so the generic dispatcher theorem would be vacuous at such a
parameter.  The same reasoning applies verbatim to `string`.

A `string` argument block *is* an `AbiArg.bytes` block — relative offset word
in the head area, length word then right-padded payload in the tail.  The two
types part ways only in the textual signature that feeds the selector hash,
which is upstream of everything here.  So the encoder is reused as-is and the
binder side is transported with
`Verity.SourceSemantics.DynamicAbi.bindExternalParam_string_eq_bytes`
(verity#2085).
-/

namespace Compiler.Proofs.IRGeneration

open Compiler
open Compiler.CompilationModel
open Compiler.Proofs.AbiEncoding
open Dispatch

namespace StringParamDispatch

/-- The external ABI binder is total on a single `string` entrypoint parameter
when the transaction arguments are a real ABI encoding.  This is exactly the
`hbindTotal` obligation of the generic dispatcher theorem. -/
theorem bindExternalParams_total_of_string_calldata
    (model : CompilationModel) (tx : IRTransaction)
    (name : String) (value : AbiBytes)
    (hwf : value.WellFormed)
    (hargs : tx.args = abiEncodeArgs [AbiArg.bytes value])
    (hsize : 4 + 32 * tx.args.length < Compiler.Constants.evmModulus)
    (hparams : ∀ fn ∈ selectorDispatchedFunctions model,
      fn.params = [{ name := name, ty := ParamType.string }]) :
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
    exact bindExternalParams_string_of_abiEncodeArgs tx.functionSelector name value hwf
      (by rw [← hargs]; exact hsize)
  exact ⟨_, hbind⟩

/-- Whole-contract dispatcher correctness for entrypoints taking a `string`
parameter.  `hbindTotal` is gone: it is discharged from the ABI encoding, so
the statement is non-vacuous at `string`. -/
theorem interpretContract_correct_of_functions_string_param
    (P : FunctionSpec → Nat → IRFunction → Prop)
    (model : CompilationModel) (selectors : List Nat)
    (irFns : List IRFunction) (tx : IRTransaction)
    (initialWorld : Verity.ContractState)
    (name : String) (value : AbiBytes)
    (hwf : value.WellFormed)
    (hargs : tx.args = abiEncodeArgs [AbiArg.bytes value])
    (hsize : 4 + 32 * tx.args.length < Compiler.Constants.evmModulus)
    (hparams : ∀ fn ∈ selectorDispatchedFunctions model,
      fn.params = [{ name := name, ty := ParamType.string }])
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
    (bindExternalParams_total_of_string_calldata model tx name value hwf hargs hsize hparams)
    hfunction

end StringParamDispatch

end Compiler.Proofs.IRGeneration
