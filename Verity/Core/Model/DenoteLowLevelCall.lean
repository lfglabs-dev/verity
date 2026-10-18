import Verity.Core.Model.DenoteByteExternalCalls

/-!
Bridge from the closed Denote transports for `<address>.code.length` and the
optional-bool low-level `.call(bytes)` to the byte-exact boundary of
`DenoteExternalCode` and `DenoteByteExternalCalls`.

* The code-length arm binds exactly `DenoteExternalCode.extCodeSize`.
* The request the low-level call transport hands to the adversary is a
  `DenoteByteExternalCalls.callBytesRequest` from the prepared frame.
* The transport continues with result `1` exactly when
  `DenoteByteExternalCalls.decodeOptionalBoolCall` accepts the observation; a
  decoded `false` continues with result `0` (the caller's own error is a separate
  `require`), and every other decoder rejection is a revert of the transport.
-/
namespace Compiler.CompilationModel.DenoteLowLevelCall

open Compiler.CompilationModel
open Denote DenoteByteExternalCalls ByteExternalCall

/-! ## Code length -/

theorem extCodeSize_module_beq_self (resultVar : String) :
    (Compiler.ECM.SolidityExtCodeSize.module resultVar ==
      Compiler.ECM.SolidityExtCodeSize.module resultVar) = true := by
  simp [BEq.beq, Compiler.ECM.SolidityExtCodeSize.module, List.beq]
  exact ⟨⟨⟨rfl, rfl⟩, rfl⟩, beq_self_eq_true (some (Compiler.ECM.ByteTransport.extCodeSize resultVar))⟩

theorem executeByteExtCodeSize_eq (oracle : DenoteOracle) (fields : List Field)
    (state : DenoteState) (resultVar : String) (target : Expr) (address : Nat)
    (htarget : evalExprList oracle fields state [target] = some [address]) :
    executeByteExtCodeSize oracle fields state
        (Compiler.ECM.SolidityExtCodeSize.module resultVar) resultVar [target] =
      .ok (.continue { state with
        bindings := bindValue state.bindings resultVar
          (DenoteExternalCode.extCodeSize state.world (Verity.Core.Address.ofNat address)) }) := by
  simp [executeByteExtCodeSize, htarget, extCodeSize_module_beq_self]
  rfl

/-- An account without code has code length zero. -/
theorem executeByteExtCodeSize_of_code_nil (oracle : DenoteOracle) (fields : List Field)
    (state : DenoteState) (resultVar : String) (target : Expr) (address : Nat)
    (htarget : evalExprList oracle fields state [target] = some [address])
    (hcode : (state.world.accountWorld (Verity.Core.Address.ofNat address)).code = []) :
    executeByteExtCodeSize oracle fields state
        (Compiler.ECM.SolidityExtCodeSize.module resultVar) resultVar [target] =
      .ok (.continue { state with bindings := bindValue state.bindings resultVar 0 }) := by
  simp [executeByteExtCodeSize_eq oracle fields state resultVar target address htarget, hcode]

/-! ## Request shape -/

theorem prepareByteWordCall_request (kind : Kind) (oracle : DenoteOracle)
    (fields : List Field) (state : DenoteState) (resultVar : String)
    (selector numWordArgs : Nat) (args : List Expr) (bumpBeforeCall : Bool)
    (prepared : ByteStaticPreparation)
    (hprepare : prepareByteWordCall kind oracle fields state resultVar selector numWordArgs args
      bumpBeforeCall = .ok prepared) :
    prepared.request.kind = kind ∧ prepared.request.value = 0 ∧
      prepared.request.caller = prepared.frame.world.thisAddress.val ∧
      prepared.request.target < 2^160 := by
  unfold prepareByteWordCall at hprepare
  simp only [bind, Except.bind, pure, Except.pure] at hprepare
  repeat' split at hprepare
  all_goals first
    | (cases hprepare; exact ⟨rfl, rfl, rfl, Nat.mod_lt _ (by decide)⟩)
    | (simp at hprepare)

/-- The low-level call transport asks the adversary exactly for a value-free
`callBytesRequest` from the prepared frame. -/
theorem prepareByteWordCall_call_eq_callBytesRequest (oracle : DenoteOracle)
    (fields : List Field) (state : DenoteState) (resultVar : String)
    (selector numWordArgs : Nat) (args : List Expr) (bumpBeforeCall : Bool)
    (prepared : ByteStaticPreparation)
    (hprepare : prepareByteWordCall .call oracle fields state resultVar selector numWordArgs args
      bumpBeforeCall = .ok prepared) :
    prepared.request = callBytesRequest { frame := prepared.frame }
      (Verity.Core.Address.ofNat prepared.request.target) prepared.request.calldata
      prepared.request.gas := by
  obtain ⟨hkind, hvalue, hcaller, htarget⟩ :=
    prepareByteWordCall_request .call oracle fields state resultVar selector numWordArgs args
      bumpBeforeCall prepared hprepare
  have hmod : prepared.request.target % Verity.Core.Address.modulus = prepared.request.target :=
    Nat.mod_eq_of_lt htarget
  cases hrequest : prepared.request
  simp_all [callBytesRequest]

/-! ## Optional-bool decoding -/

@[simp] theorem leadingWord_eq_firstWord (data : Bytes) : leadingWord data = firstWord data := rfl

theorem classifyOptionalBoolCall_failure (data : Bytes) :
    classifyOptionalBoolCall false data = .forward data := rfl

theorem classifyOptionalBoolCall_empty : classifyOptionalBoolCall true [] = .decoded 1 := rfl

/-- The acceptance condition of `decodeOptionalBoolCall` is classification as
the decoded `bool` `true`. -/
theorem optionalBoolAccepts_iff (success : Bool) (data : Bytes) :
    (success = true ∧ (data.isEmpty ∨ (32 ≤ data.length ∧ firstWord data = 1))) ↔
      classifyOptionalBoolCall success data = .decoded 1 := by
  unfold classifyOptionalBoolCall
  cases success
  · simp
  · by_cases hempty : data = []
    · simp [hempty]
    · by_cases hshort : data.length < 32
      · simp [hempty, hshort]
        omega
      · by_cases hbig : 1 < firstWord data
        · simp [hempty, hshort, hbig]
          omega
        · simp [hempty, hshort, hbig]
          omega

/-- The transport's result is `1` exactly when the B0 optional-bool decoder
accepts the observation. -/
theorem decodeOptionalBoolCall_eq_return_iff_classify (observed : Observation) :
    decodeOptionalBoolCall observed = .return 1 observed.state.frame ↔
      classifyOptionalBoolCall observed.success observed.state.returndata = .decoded 1 := by
  rw [decodeOptionalBoolCall_eq_return_iff]
  exact optionalBoolAccepts_iff _ _

/-- Every observation the transport does not bind to `1` is rejected by the B0
decoder: a decoded `false` (the importer composes the caller's own error as a
`require` on the result), a forwarded failure, or malformed returndata. -/
theorem decodeOptionalBoolCall_of_classify_ne_one (observed : Observation)
    (hreject : classifyOptionalBoolCall observed.success observed.state.returndata ≠ .decoded 1) :
    decodeOptionalBoolCall observed = .revertWithData [] := by
  unfold decodeOptionalBoolCall
  rw [if_neg]
  exact fun haccept => hreject ((optionalBoolAccepts_iff _ _).mp haccept)

/-- A decoded word is always a valid ABI `bool`. -/
theorem classifyOptionalBoolCall_decoded_le_one (success : Bool) (data : Bytes) (word : Nat)
    (hdecoded : classifyOptionalBoolCall success data = .decoded word) : word ≤ 1 := by
  unfold classifyOptionalBoolCall at hdecoded
  split at hdecoded
  · cases hdecoded
  · split at hdecoded
    · cases hdecoded
      exact Nat.le_refl 1
    · split at hdecoded
      · cases hdecoded
      · split at hdecoded
        · cases hdecoded
        · cases hdecoded
          omega

end Compiler.CompilationModel.DenoteLowLevelCall
