import Contracts.Smoke.ExternalCalls

namespace Contracts.Smoke

open Contracts
open Verity hiding pure bind
open Verity.EVM.Uint256
open Verity.Stdlib.Math

namespace SpecGenSmoke

#gen_spec storage_for2_spec for2 (x : Uint256) (y : Uint256)
  (0, (fun st => add (st.storage 0) (add x y)), Verity.Specs.sameAddrMapContext)

#gen_spec storage_for2_extra_spec for2 (x : Uint256) (y : Uint256)
  (0, (fun st => add (st.storage 0) (add x y)), Verity.Specs.sameAddrMapContext,
    (fun _ s' => s'.storage 0 >= x))

#gen_spec_addr addr_for2_spec for2 (owner : Address) (_salt : Uint256)
  (0, (fun _ => owner), Verity.Specs.sameStorageMapContext)

#gen_spec_addr addr_for2_extra_spec for2 (owner : Address) (salt : Uint256)
  (0, (fun _ => owner), Verity.Specs.sameStorageMapContext,
    (fun _ s' => s'.storage 0 = owner.toNat ∧ salt = salt))

#gen_spec_addr_storage addr_storage_for2_spec for2 (owner : Address) (value : Uint256)
  (0, 2, (fun _ => owner), (fun _ => value), Verity.Specs.sameStorageMapsContext)

#gen_spec_addr_storage addr_storage_for2_extra_spec for2 (owner : Address) (value : Uint256)
  (0, 2, (fun _ => owner), (fun _ => value), Verity.Specs.sameStorageMapsContext,
    (fun _ s' => s'.storage 2 = value))

example (x y : Uint256) (s s' : ContractState) :
    storage_for2_spec x y s s' =
      Verity.Specs.storageUpdateSpec 0 (fun st => add (st.storage 0) (add x y))
        Verity.Specs.sameAddrMapContext s s' := rfl

example (owner : Address) (salt : Uint256) (s s' : ContractState) :
    addr_for2_spec owner salt s s' =
      Verity.Specs.storageAddrUpdateSpec 0 (fun _ => owner)
        Verity.Specs.sameStorageMapContext s s' := rfl

example (owner : Address) (value : Uint256) (s s' : ContractState) :
    addr_storage_for2_spec owner value s s' =
      Verity.Specs.storageAddrStorageUpdateSpec 0 2 (fun _ => owner) (fun _ => value)
        Verity.Specs.sameStorageMapsContext s s' := rfl

end SpecGenSmoke

#check_contract Contracts.Counter
#check_contract Uint256PowSmoke
#check_contract UintMapSmoke
#check_contract Bytes32Smoke
#check_contract StorageAddressArraySmoke
#check_contract StorageBoolArraySmoke
#check_contract StorageBytes32ArraySmoke
#check_contract MappingWordSmoke
#check_contract StorageWordsSmoke
#check_contract CustomErrorSmoke
#check_contract SafeMulRequireSmoke
#check_contract ArithmeticPanicSmoke
#check_contract MulDiv512Smoke
#check_contract IntrinsicClzSmoke
#check_contract ByteBuiltinSmoke
#check_contract SignedBuiltinSmoke
#check_contract StatelessSmoke
#check_contract SpecialEntrypointSmoke
#check_contract TupleSmoke
#check_contract NamedStructParamSmoke
#check_contract NestedStructStorageSmoke
#check_contract NamedStructDynamicRootLeafProjection
#check_contract CurveCutArraySmoke
#check_contract DynamicStructArraySmoke
#check_contract PackedStorageWriteSmoke
#check_contract DirectHelperCallSmoke
#check_contract MultiReturnHelperSmoke
#check_contract ArrayHelperCallSmoke
#check_contract DirectHelperCallBytesEffectSmoke
#check_contract DirectHelperCallBytesBindSmoke
#check_contract DirectHelperCallBytesTupleSmoke
#check_contract DirectHelperCallStaticCompositeSmoke
#check_contract DirectHelperCallUint256Bytes32AliasSmoke
#check_contract ForEachMutableLocalSmoke
#check_contract Uint8Smoke
#check_contract AddressHelpersSmoke
#check_contract ZeroAddressShadowSmoke
#check_contract ContextAccessorShadowSmoke
#check_contract FunctionOverloadSmoke
#check_contract FunctionPointerParamSmoke
#check_contract HelperExternalArgumentSmoke
#check_contract BlockTimestampSmoke
#check_contract StructMappingSmoke
#check_contract FixedArrayMappingStructSmoke
#check_contract UintKeyStructMappingSmoke
#check_contract ExternalCallSmoke
#check_contract TryExternalCallSmoke
#check_contract CallResultSmoke
#check_contract LinkedExternalDynamicArgSmoke
#check_contract LinkedExternalProjectedArrayArgSmoke
#check_contract NestedStructArrayProjectionSmoke
#check_contract ExternalCallMultiReturn
#check_contract Create2SSTORE2Smoke
#check_contract CallbackABISmoke
#check_contract Contracts.Vault

namespace CheckedArithmeticObligationSmoke

def safeAddRequireSurfacesOverflowObligation : Bool :=
  match Contracts.SafeCounter.increment_model.localObligations with
  | [{ name := "checked_arithmetic_increment_1_add_no_overflow"
       obligation := "Prove `Verity.Proofs.Stdlib.Math.CheckedArithmetic.AddNoOverflow (current) (1)` for the checked arithmetic operation emitted at this entrypoint."
       proofStatus := .assumed }] => true
  | _ => false

example : safeAddRequireSurfacesOverflowObligation = true := by rfl

def safeSubRequireSurfacesUnderflowObligation : Bool :=
  match Contracts.SafeCounter.decrement_model.localObligations with
  | [{ name := "checked_arithmetic_decrement_1_sub_no_underflow"
       obligation := "Prove `Verity.Proofs.Stdlib.Math.CheckedArithmetic.SubNoUnderflow (current) (1)` for the checked arithmetic operation emitted at this entrypoint."
       proofStatus := .assumed }] => true
  | _ => false

example : safeSubRequireSurfacesUnderflowObligation = true := by rfl

def safeMulRequireSurfacesOverflowObligation : Bool :=
  match Contracts.Smoke.SafeMulRequireSmoke.multiplyStored_model.localObligations with
  | [{ name := "checked_arithmetic_multiplyStored_1_mul_no_overflow"
       obligation := "Prove `Verity.Proofs.Stdlib.Math.CheckedArithmetic.MulNoOverflow (current) (factor)` for the checked arithmetic operation emitted at this entrypoint."
       proofStatus := .assumed }] => true
  | _ => false

example : safeMulRequireSurfacesOverflowObligation = true := by rfl

end CheckedArithmeticObligationSmoke

example : TupleSmoke.setFromPair = (TupleSmoke.setFromPair : (Uint256 × Uint256) → Verity.Contract Unit) := rfl
example : TupleSmoke.getPair = (TupleSmoke.getPair : Uint256 → Verity.Contract (Uint256 × Uint256)) := rfl
example :
    TupleSmoke.processConfig =
      (TupleSmoke.processConfig : (Address × Address × Uint256) → Verity.Contract Unit) := rfl

example :
    NamedStructParamSmoke.readBorrowFee =
      (NamedStructParamSmoke.readBorrowFee :
        NamedStructParamSmoke.FeeConfig → Verity.Contract Uint256) := rfl

def namedStructExecutableReadsField : Bool :=
  let feeConfig : NamedStructParamSmoke.FeeConfig := {
    borrowTakerFeeRatio := 11
    lendMakerFeeRatio := 13
  }
  match NamedStructParamSmoke.readBorrowFee feeConfig Verity.defaultState with
  | .success value _ => value == 11
  | _ => false

example : namedStructExecutableReadsField = true := by decide
example : Uint8Smoke.acceptSig = (Uint8Smoke.acceptSig : (Uint256 × Uint256 × Uint256) → Verity.Contract Unit) := rfl
example : ExternalCallSmoke.storeEcho = (ExternalCallSmoke.storeEcho : Uint256 → Verity.Contract Unit) := rfl

example :
    (Compiler.CompilationModel.FunctionSpec.body
      (Contracts.Counter.increment_model : Compiler.CompilationModel.FunctionSpec)) =
    Contracts.Counter.increment_modelBody := by
  simpa using Contracts.Counter.increment_semantic_preservation

example :
    (Compiler.CompilationModel.FunctionSpec.body
      (Contracts.Counter.increment_model : Compiler.CompilationModel.FunctionSpec)) =
    Contracts.Counter.increment_modelBody := by
  simpa using Contracts.Counter.increment_bridge

example :
    (Compiler.CompilationModel.FunctionSpec.body
      (Contracts.Counter.decrement_model : Compiler.CompilationModel.FunctionSpec)) =
    Contracts.Counter.decrement_modelBody := by
  simpa using Contracts.Counter.decrement_semantic_preservation

example :
    (Compiler.CompilationModel.FunctionSpec.body
      (Contracts.Counter.decrement_model : Compiler.CompilationModel.FunctionSpec)) =
    Contracts.Counter.decrement_modelBody := by
  simpa using Contracts.Counter.decrement_bridge

example :
    (Compiler.CompilationModel.FunctionSpec.body
      (Contracts.Counter.getCount_model : Compiler.CompilationModel.FunctionSpec)) =
    Contracts.Counter.getCount_modelBody := by
  simpa using Contracts.Counter.getCount_semantic_preservation

example :
    (Compiler.CompilationModel.FunctionSpec.body
      (Contracts.Counter.getCount_model : Compiler.CompilationModel.FunctionSpec)) =
    Contracts.Counter.getCount_modelBody := by
  simpa using Contracts.Counter.getCount_bridge

example :
    (Compiler.CompilationModel.FunctionSpec.body
      (Contracts.SimpleStorage.store_model : Compiler.CompilationModel.FunctionSpec)) =
    Contracts.SimpleStorage.store_modelBody := by
  simpa using Contracts.SimpleStorage.store_semantic_preservation

example :
    (Compiler.CompilationModel.FunctionSpec.body
      (Contracts.SimpleStorage.retrieve_model : Compiler.CompilationModel.FunctionSpec)) =
    Contracts.SimpleStorage.retrieve_modelBody := by
  simpa using Contracts.SimpleStorage.retrieve_semantic_preservation

example :
    (Compiler.CompilationModel.FunctionSpec.body
      (Contracts.Owned.transferOwnership_model : Compiler.CompilationModel.FunctionSpec)) =
    Contracts.Owned.transferOwnership_modelBody := by
  simpa using Contracts.Owned.transferOwnership_semantic_preservation

example :
    (Compiler.CompilationModel.FunctionSpec.body
      (Contracts.Owned.getOwner_model : Compiler.CompilationModel.FunctionSpec)) =
    Contracts.Owned.getOwner_modelBody := by
  simpa using Contracts.Owned.getOwner_semantic_preservation

example :
    (Compiler.CompilationModel.FunctionSpec.body
      (Contracts.SafeCounter.increment_model : Compiler.CompilationModel.FunctionSpec)) =
    Contracts.SafeCounter.increment_modelBody := by
  simpa using Contracts.SafeCounter.increment_semantic_preservation

example :
    (Compiler.CompilationModel.FunctionSpec.body
      (Contracts.SafeCounter.decrement_model : Compiler.CompilationModel.FunctionSpec)) =
    Contracts.SafeCounter.decrement_modelBody := by
  simpa using Contracts.SafeCounter.decrement_semantic_preservation

example :
    (Compiler.CompilationModel.FunctionSpec.body
      (Contracts.SafeCounter.getCount_model : Compiler.CompilationModel.FunctionSpec)) =
    Contracts.SafeCounter.getCount_modelBody := by
  simpa using Contracts.SafeCounter.getCount_semantic_preservation

example :
    (Compiler.CompilationModel.FunctionSpec.body
      (Contracts.OwnedCounter.increment_model : Compiler.CompilationModel.FunctionSpec)) =
    Contracts.OwnedCounter.increment_modelBody := by
  simpa using Contracts.OwnedCounter.increment_semantic_preservation

example :
    (Compiler.CompilationModel.FunctionSpec.body
      (Contracts.OwnedCounter.decrement_model : Compiler.CompilationModel.FunctionSpec)) =
    Contracts.OwnedCounter.decrement_modelBody := by
  simpa using Contracts.OwnedCounter.decrement_semantic_preservation

example :
    (Compiler.CompilationModel.FunctionSpec.body
      (Contracts.OwnedCounter.getCount_model : Compiler.CompilationModel.FunctionSpec)) =
    Contracts.OwnedCounter.getCount_modelBody := by
  simpa using Contracts.OwnedCounter.getCount_semantic_preservation

example :
    (Compiler.CompilationModel.FunctionSpec.body
      (Contracts.OwnedCounter.getOwner_model : Compiler.CompilationModel.FunctionSpec)) =
    Contracts.OwnedCounter.getOwner_modelBody := by
  simpa using Contracts.OwnedCounter.getOwner_semantic_preservation

example :
    (Compiler.CompilationModel.FunctionSpec.body
      (Contracts.OwnedCounter.transferOwnership_model : Compiler.CompilationModel.FunctionSpec)) =
    Contracts.OwnedCounter.transferOwnership_modelBody := by
  simpa using Contracts.OwnedCounter.transferOwnership_semantic_preservation

example :
    (Compiler.CompilationModel.FunctionSpec.body
      (Contracts.Ledger.deposit_model : Compiler.CompilationModel.FunctionSpec)) =
    Contracts.Ledger.deposit_modelBody := by
  simpa using Contracts.Ledger.deposit_semantic_preservation

example :
    (Compiler.CompilationModel.FunctionSpec.body
      (Contracts.Ledger.withdraw_model : Compiler.CompilationModel.FunctionSpec)) =
    Contracts.Ledger.withdraw_modelBody := by
  simpa using Contracts.Ledger.withdraw_semantic_preservation

example :
    (Compiler.CompilationModel.FunctionSpec.body
      (Contracts.Ledger.transfer_model : Compiler.CompilationModel.FunctionSpec)) =
    Contracts.Ledger.transfer_modelBody := by
  simpa using Contracts.Ledger.transfer_semantic_preservation

example :
    (Compiler.CompilationModel.FunctionSpec.body
      (Contracts.Ledger.getBalance_model : Compiler.CompilationModel.FunctionSpec)) =
    Contracts.Ledger.getBalance_modelBody := by
  simpa using Contracts.Ledger.getBalance_semantic_preservation

example :
    (Compiler.CompilationModel.FunctionSpec.body
      (Contracts.SimpleToken.mint_model : Compiler.CompilationModel.FunctionSpec)) =
    Contracts.SimpleToken.mint_modelBody := by
  simpa using Contracts.SimpleToken.mint_semantic_preservation

example :
    (Compiler.CompilationModel.FunctionSpec.body
      (Contracts.SimpleToken.transfer_model : Compiler.CompilationModel.FunctionSpec)) =
    Contracts.SimpleToken.transfer_modelBody := by
  simpa using Contracts.SimpleToken.transfer_semantic_preservation

example :
    (Compiler.CompilationModel.FunctionSpec.body
      (Contracts.SimpleToken.balanceOf_model : Compiler.CompilationModel.FunctionSpec)) =
    Contracts.SimpleToken.balanceOf_modelBody := by
  simpa using Contracts.SimpleToken.balanceOf_semantic_preservation

example :
    (Compiler.CompilationModel.FunctionSpec.body
      (Contracts.SimpleToken.totalSupply_model : Compiler.CompilationModel.FunctionSpec)) =
    Contracts.SimpleToken.totalSupply_modelBody := by
  simpa using Contracts.SimpleToken.totalSupply_semantic_preservation

example :
    (Compiler.CompilationModel.FunctionSpec.body
      (Contracts.SimpleToken.owner_model : Compiler.CompilationModel.FunctionSpec)) =
    Contracts.SimpleToken.owner_modelBody := by
  simpa using Contracts.SimpleToken.owner_semantic_preservation

example :
    (Compiler.CompilationModel.FunctionSpec.body
      (Contracts.ERC20.mint_model : Compiler.CompilationModel.FunctionSpec)) =
    Contracts.ERC20.mint_modelBody := by
  simpa using Contracts.ERC20.mint_semantic_preservation

example :
    (Compiler.CompilationModel.FunctionSpec.body
      (Contracts.ERC20.transfer_model : Compiler.CompilationModel.FunctionSpec)) =
    Contracts.ERC20.transfer_modelBody := by
  simpa using Contracts.ERC20.transfer_semantic_preservation

example :
    (Compiler.CompilationModel.FunctionSpec.body
      (Contracts.ERC20.approve_model : Compiler.CompilationModel.FunctionSpec)) =
    Contracts.ERC20.approve_modelBody := by
  simpa using Contracts.ERC20.approve_semantic_preservation

example :
    (Compiler.CompilationModel.FunctionSpec.body
      (Contracts.ERC20.transferFrom_model : Compiler.CompilationModel.FunctionSpec)) =
    Contracts.ERC20.transferFrom_modelBody := by
  simpa using Contracts.ERC20.transferFrom_semantic_preservation

example :
    (Compiler.CompilationModel.FunctionSpec.body
      (Contracts.ERC20.balanceOf_model : Compiler.CompilationModel.FunctionSpec)) =
    Contracts.ERC20.balanceOf_modelBody := by
  simpa using Contracts.ERC20.balanceOf_semantic_preservation

example :
    (Compiler.CompilationModel.FunctionSpec.body
      (Contracts.ERC20.allowanceOf_model : Compiler.CompilationModel.FunctionSpec)) =
    Contracts.ERC20.allowanceOf_modelBody := by
  simpa using Contracts.ERC20.allowanceOf_semantic_preservation

example :
    (Compiler.CompilationModel.FunctionSpec.body
      (Contracts.ERC20.totalSupply_model : Compiler.CompilationModel.FunctionSpec)) =
    Contracts.ERC20.totalSupply_modelBody := by
  simpa using Contracts.ERC20.totalSupply_semantic_preservation

example :
    (Compiler.CompilationModel.FunctionSpec.body
      (Contracts.ERC20.owner_model : Compiler.CompilationModel.FunctionSpec)) =
    Contracts.ERC20.owner_modelBody := by
  simpa using Contracts.ERC20.owner_semantic_preservation

example :
    (Compiler.CompilationModel.FunctionSpec.body
      (GenericECMReadSmoke.snapshotQuote_model : Compiler.CompilationModel.FunctionSpec)) =
    GenericECMReadSmoke.snapshotQuote_modelBody := by
  simpa using GenericECMReadSmoke.snapshotQuote_semantic_preservation

example :
    GenericECMReadSmoke.snapshotQuote_modelBody =
      [ Compiler.CompilationModel.Stmt.ecm
          ((fun resultVar => Compiler.Modules.Oracle.oracleReadUint256Module resultVar 0x12345678 1)
            "quote")
          [ Compiler.CompilationModel.Expr.param "oracle"
          , Compiler.CompilationModel.Expr.param "asset"
          ]
      , Compiler.CompilationModel.Stmt.setStorage
          "lastQuote"
          (Compiler.CompilationModel.Expr.localVar "quote")
      , Compiler.CompilationModel.Stmt.return
          (Compiler.CompilationModel.Expr.localVar "quote")
      ] := rfl

example :
    (Compiler.CompilationModel.FunctionSpec.body
      (GenericECMMultiResultSmoke.addPoints_model : Compiler.CompilationModel.FunctionSpec)) =
    GenericECMMultiResultSmoke.addPoints_modelBody := by
  simpa using GenericECMMultiResultSmoke.addPoints_semantic_preservation

example :
    GenericECMMultiResultSmoke.addPoints_modelBody =
      [ Compiler.CompilationModel.Stmt.ecm
          (Compiler.Modules.Precompiles.bn256AddModule "sumX" "sumY")
          [ Compiler.CompilationModel.Expr.param "x1"
          , Compiler.CompilationModel.Expr.param "y1"
          , Compiler.CompilationModel.Expr.param "x2"
          , Compiler.CompilationModel.Expr.param "y2"
          ]
      , Compiler.CompilationModel.Stmt.setStorage
          "lastX"
          (Compiler.CompilationModel.Expr.localVar "sumX")
      , Compiler.CompilationModel.Stmt.setStorage
          "lastY"
          (Compiler.CompilationModel.Expr.localVar "sumY")
      , Compiler.CompilationModel.Stmt.stop
      ] := rfl

example :
    (Compiler.CompilationModel.FunctionSpec.body
      (GenericECMWriteSmoke.runEffect_model : Compiler.CompilationModel.FunctionSpec)) =
    GenericECMWriteSmoke.runEffect_modelBody := by
  simpa using GenericECMWriteSmoke.runEffect_semantic_preservation

example :
    GenericECMWriteSmoke.runEffect_modelBody =
      [ Compiler.CompilationModel.Stmt.ecm
          genericECMEffectDemoModule
          [ Compiler.CompilationModel.Expr.param "lhs"
          , Compiler.CompilationModel.Expr.param "rhs"
          ]
      , Compiler.CompilationModel.Stmt.stop
      ] := rfl

example :
    (Compiler.CompilationModel.FunctionSpec.body
      (CallWithValueSmoke.execute_model : Compiler.CompilationModel.FunctionSpec)) =
    CallWithValueSmoke.execute_modelBody := by
  simpa using CallWithValueSmoke.execute_semantic_preservation

example :
    CallWithValueSmoke.execute_modelBody =
      [ Compiler.CompilationModel.Stmt.ecm
          Compiler.Modules.Calls.callWithValueModule
          [ Compiler.CompilationModel.Expr.param "target"
          , Compiler.CompilationModel.Expr.param "value"
          , Compiler.CompilationModel.Expr.param "dataOffset"
          , Compiler.CompilationModel.Expr.param "dataSize"
          ]
      , Compiler.CompilationModel.Stmt.stop
      ] := rfl

example :
    CallWithValueSmoke.executeBytes_modelBody =
      [ Compiler.CompilationModel.Stmt.ecm
          (Compiler.Modules.Calls.callWithValueBytesModule "data")
          [ Compiler.CompilationModel.Expr.param "target"
          , Compiler.CompilationModel.Expr.param "value"
          ]
      , Compiler.CompilationModel.Stmt.stop
      ] := rfl

example :
    (Compiler.CompilationModel.FunctionSpec.body
      (BubblingValueCallECMSmoke.forwardNoOutput_model : Compiler.CompilationModel.FunctionSpec)) =
    BubblingValueCallECMSmoke.forwardNoOutput_modelBody := by
  simpa using BubblingValueCallECMSmoke.forwardNoOutput_semantic_preservation

example :
    BubblingValueCallECMSmoke.forwardNoOutput_modelBody =
      [ Compiler.CompilationModel.Stmt.ecm
          Compiler.Modules.Calls.bubblingValueCallNoOutputModule
          [ Compiler.CompilationModel.Expr.param "target"
          , Compiler.CompilationModel.Expr.param "ethValue"
          , Compiler.CompilationModel.Expr.param "inputOffset"
          , Compiler.CompilationModel.Expr.param "inputSize"
          ]
      , Compiler.CompilationModel.Stmt.stop
      ] := rfl

example :
    (LowLevelTryCatchSmoke.catchFailure.run Verity.defaultState).getValue? = some 0 := by
  decide

example :
    (LowLevelTryCatchSmoke.skipCatchOnSuccess.run Verity.defaultState).getValue? = some 0 := by
  decide

example :
    ((LowLevelTryCatchSmoke.catchFailureWithShadowedParam 5).run Verity.defaultState).getValue? = some 0 := by
  decide

example :
    LowLevelTryCatchSmoke.catchFailure_modelBody =
      [ Compiler.CompilationModel.Stmt.letVar "verity_try_success"
          (Compiler.CompilationModel.Expr.call
            (Compiler.CompilationModel.Expr.literal 0)
            (Compiler.CompilationModel.Expr.literal 0)
            (Compiler.CompilationModel.Expr.literal 1)
            (Compiler.CompilationModel.Expr.literal 0)
            (Compiler.CompilationModel.Expr.literal 0)
            (Compiler.CompilationModel.Expr.literal 0)
            (Compiler.CompilationModel.Expr.literal 0))
      , Compiler.CompilationModel.Stmt.ite
          (Compiler.CompilationModel.Expr.eq
            (Compiler.CompilationModel.Expr.localVar "verity_try_success")
            (Compiler.CompilationModel.Expr.literal 0))
          [ Compiler.CompilationModel.Stmt.setStorage
              "lastOutcome"
              (Compiler.CompilationModel.Expr.literal 7)
          ]
          []
      , Compiler.CompilationModel.Stmt.letVar
          "current"
          (Compiler.CompilationModel.Expr.storage "lastOutcome")
      , Compiler.CompilationModel.Stmt.return
          (Compiler.CompilationModel.Expr.localVar "current")
      ] := rfl

example :
    LowLevelTryCatchSmoke.catchFailureWithShadowedParam_modelBody =
      [ Compiler.CompilationModel.Stmt.letVar "verity_try_success_1"
          (Compiler.CompilationModel.Expr.call
            (Compiler.CompilationModel.Expr.literal 0)
            (Compiler.CompilationModel.Expr.literal 0)
            (Compiler.CompilationModel.Expr.literal 1)
            (Compiler.CompilationModel.Expr.literal 0)
            (Compiler.CompilationModel.Expr.literal 0)
            (Compiler.CompilationModel.Expr.literal 0)
            (Compiler.CompilationModel.Expr.literal 0))
      , Compiler.CompilationModel.Stmt.ite
          (Compiler.CompilationModel.Expr.eq
          (Compiler.CompilationModel.Expr.localVar "verity_try_success_1")
            (Compiler.CompilationModel.Expr.literal 0))
          [ Compiler.CompilationModel.Stmt.setStorage
              "lastOutcome"
              (Compiler.CompilationModel.Expr.literal 11)
          ]
          []
      , Compiler.CompilationModel.Stmt.letVar
          "current"
          (Compiler.CompilationModel.Expr.storage "lastOutcome")
      , Compiler.CompilationModel.Stmt.return
          (Compiler.CompilationModel.Expr.localVar "current")
      ] := rfl

example :
    (Compiler.CompilationModel.FunctionSpec.body
      (Contracts.ERC721.mint_model : Compiler.CompilationModel.FunctionSpec)) =
    Contracts.ERC721.mint_modelBody := by
  simpa using Contracts.ERC721.mint_semantic_preservation

example :
    (Compiler.CompilationModel.FunctionSpec.body
      (Contracts.ERC721.transferFrom_model : Compiler.CompilationModel.FunctionSpec)) =
    Contracts.ERC721.transferFrom_modelBody := by
  simpa using Contracts.ERC721.transferFrom_semantic_preservation

example :
    (Compiler.CompilationModel.FunctionSpec.body
      (Contracts.ERC721.ownerOf_model : Compiler.CompilationModel.FunctionSpec)) =
    Contracts.ERC721.ownerOf_modelBody := by
  simpa using Contracts.ERC721.ownerOf_semantic_preservation

example :
    (Compiler.CompilationModel.FunctionSpec.body
      (Contracts.ERC721.approve_model : Compiler.CompilationModel.FunctionSpec)) =
    Contracts.ERC721.approve_modelBody := by
  simpa using Contracts.ERC721.approve_semantic_preservation

example :
    (Compiler.CompilationModel.FunctionSpec.body
      (Contracts.ERC721.getApproved_model : Compiler.CompilationModel.FunctionSpec)) =
    Contracts.ERC721.getApproved_modelBody := by
  simpa using Contracts.ERC721.getApproved_semantic_preservation

end Contracts.Smoke
