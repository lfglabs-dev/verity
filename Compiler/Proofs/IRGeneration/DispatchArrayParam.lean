import Compiler.Proofs.IRGeneration.DispatchGeneric
import Compiler.Proofs.AbiEncoding

/-!
# Dispatcher correctness at a `T[]` external parameter

The `bytes` module explains why `hbindTotal` cannot be left as a hypothesis for
a dynamic parameter: on arbitrary calldata the external binder returns `none`,
so the generic dispatcher theorem would be vacuous at such a parameter.  The
same reasoning applies to a dynamic array.

A `T[]` argument block is a relative offset word in the head area, then an
element count followed by one normalised word per element in the tail — which is
`AbiArg.scalarArray`.  The element type must be single-word static, so the
loader's strided payload guard reduces to the plain word bound (verity#2085).
-/

namespace Compiler.Proofs.IRGeneration

open Compiler
open Compiler.CompilationModel
open Compiler.Proofs.AbiEncoding
open Dispatch

namespace ArrayParamDispatch

/-- The external ABI binder is total on a single `T[]` entrypoint parameter when
the transaction arguments are a real ABI encoding.  This is exactly the
`hbindTotal` obligation of the generic dispatcher theorem. -/
theorem bindExternalParams_total_of_array_calldata
    (model : CompilationModel) (tx : IRTransaction)
    (name : String) (elementType : ParamType) (values : List Nat)
    (helem : isSingleWordStaticParamType elementType = true)
    (hargs : tx.args = abiEncodeArgs [AbiArg.scalarArray elementType values])
    (hsize : 4 + 32 * tx.args.length < Compiler.Constants.evmModulus)
    (hparams : ∀ fn ∈ selectorDispatchedFunctions model,
      fn.params = [{ name := name, ty := ParamType.array elementType }]) :
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
          , (s!"{name}_length", values.length)
          , (s!"{name}_tail_head_end", 68)
          , (s!"{name}_tail_remaining", 32 * values.length)
          , (s!"{name}_data_offset", 68) ] := by
    rw [hparams fn hfn, hargs]
    exact bindExternalParams_scalarArray_of_abiEncodeArgs tx.functionSelector name elementType
      values helem (by rw [← hargs]; exact hsize)
  exact ⟨_, hbind⟩

/-- Whole-contract dispatcher correctness for entrypoints taking a `T[]`
parameter.  `hbindTotal` is gone: it is discharged from the ABI encoding, so the
statement is non-vacuous at `T[]`. -/
theorem interpretContract_correct_of_functions_array_param
    (P : FunctionSpec → Nat → IRFunction → Prop)
    (model : CompilationModel) (selectors : List Nat)
    (irFns : List IRFunction) (tx : IRTransaction)
    (initialWorld : Verity.ContractState)
    (name : String) (elementType : ParamType) (values : List Nat)
    (helem : isSingleWordStaticParamType elementType = true)
    (hargs : tx.args = abiEncodeArgs [AbiArg.scalarArray elementType values])
    (hsize : 4 + 32 * tx.args.length < Compiler.Constants.evmModulus)
    (hparams : ∀ fn ∈ selectorDispatchedFunctions model,
      fn.params = [{ name := name, ty := ParamType.array elementType }])
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
    (bindExternalParams_total_of_array_calldata model tx name elementType values helem hargs
      hsize hparams)
    hfunction

end ArrayParamDispatch

end Compiler.Proofs.IRGeneration
