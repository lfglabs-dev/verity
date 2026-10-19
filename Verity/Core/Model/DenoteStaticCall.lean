import Verity.Core.Model.DenoteLowLevelCall

/-!
Bridge from the closed Denote transports for typed-interface `staticcall`
(`staticBool`, `staticBytesUint256`, `staticBytesBool`) to the byte-exact
boundary of `DenoteByteExternalCalls`.

* Both word-calldata and memory-payload staticcall preparations ask the
  adversary for a `DenoteByteExternalCalls.staticBytesRequest` from the
  prepared frame.
* `classifyStaticBoolCall` decodes `word` iff `decodeStaticBool` returns `word`,
  and every decoded word is a valid ABI `bool` (`word ≤ 1`).
* `classifyStaticWordCall` decodes `word` iff `decodeStaticUint256` returns
  `word`.
-/
namespace Compiler.CompilationModel.DenoteStaticCall

open Compiler.CompilationModel
open Denote DenoteByteExternalCalls ByteExternalCall

/-! ## Request shape -/

theorem prepareByteStaticCall_eq_staticBytesRequest (oracle : DenoteOracle)
    (fields : List Field) (state : DenoteState) (resultVar : String)
    (selector numStaticArgs : Nat) (args : List Expr)
    (prepared : ByteStaticPreparation)
    (hprepare : prepareByteStaticCall oracle fields state resultVar selector numStaticArgs args =
      .ok prepared) :
    prepared.request = staticBytesRequest { frame := prepared.frame }
      (Verity.Core.Address.ofNat prepared.request.target) prepared.request.calldata
      prepared.request.gas := by
  obtain ⟨hkind, hvalue, hcaller, htarget⟩ :=
    DenoteLowLevelCall.prepareByteWordCall_request .staticcall oracle fields state resultVar
      selector numStaticArgs args true prepared hprepare
  have hmod : prepared.request.target % Verity.Core.Address.modulus = prepared.request.target :=
    Nat.mod_eq_of_lt htarget
  cases hrequest : prepared.request
  simp_all [staticBytesRequest]

theorem prepareByteStaticBytesCall_request (oracle : DenoteOracle)
    (fields : List Field) (state : DenoteState) (resultVar : String)
    (selector : Nat) (args : List Expr) (prepared : ByteStaticPreparation)
    (hprepare : prepareByteStaticBytesCall oracle fields state resultVar selector args =
      .ok prepared) :
    prepared.request.kind = .staticcall ∧ prepared.request.value = 0 ∧
      prepared.request.caller = prepared.frame.world.thisAddress.val ∧
      prepared.request.target < 2^160 := by
  unfold prepareByteStaticBytesCall at hprepare
  simp only [bind, Except.bind, pure, Except.pure] at hprepare
  repeat' split at hprepare
  all_goals first
    | (cases hprepare; exact ⟨rfl, rfl, rfl, Nat.mod_lt _ (by decide)⟩)
    | (simp at hprepare)

theorem prepareByteStaticBytesCall_eq_staticBytesRequest (oracle : DenoteOracle)
    (fields : List Field) (state : DenoteState) (resultVar : String)
    (selector : Nat) (args : List Expr) (prepared : ByteStaticPreparation)
    (hprepare : prepareByteStaticBytesCall oracle fields state resultVar selector args =
      .ok prepared) :
    prepared.request = staticBytesRequest { frame := prepared.frame }
      (Verity.Core.Address.ofNat prepared.request.target) prepared.request.calldata
      prepared.request.gas := by
  obtain ⟨hkind, hvalue, hcaller, htarget⟩ :=
    prepareByteStaticBytesCall_request oracle fields state resultVar selector args
      prepared hprepare
  have hmod : prepared.request.target % Verity.Core.Address.modulus = prepared.request.target :=
    Nat.mod_eq_of_lt htarget
  cases hrequest : prepared.request
  simp_all [staticBytesRequest]

/-! ## Static bool and word decoding -/

theorem classifyStaticBoolCall_failure (data : Bytes) :
    classifyStaticBoolCall false data = .forward data := rfl

theorem classifyStaticBoolCall_short (data : Bytes) (hshort : data.length < 32) :
    classifyStaticBoolCall true data = .malformed := by
  simp [classifyStaticBoolCall, hshort]

theorem classifyStaticBoolCall_decoded_iff (success : Bool) (data : Bytes) (word : Nat) :
    classifyStaticBoolCall success data = .decoded word ↔
      success = true ∧ 32 ≤ data.length ∧ firstWord data ≤ 1 ∧ firstWord data = word := by
  unfold classifyStaticBoolCall
  cases success
  · simp
  · by_cases hshort : data.length < 32
    · simp [hshort]
      omega
    · by_cases hbig : 1 < firstWord data
      · simp [hshort, hbig]
        omega
      · simp [hshort, hbig]
        omega

theorem decodeStaticBool_eq_return_iff_classify (observed : Observation) (word : Nat) :
    decodeStaticBool observed = .return word observed.state.frame ↔
      classifyStaticBoolCall observed.success observed.state.returndata = .decoded word := by
  rw [classifyStaticBoolCall_decoded_iff]
  unfold decodeStaticBool
  cases hsuccess : observed.success
  · simp
  · by_cases hshort : observed.state.returndata.length < 32
    · simp [hshort]
      omega
    · by_cases hle : firstWord observed.state.returndata ≤ 1
      · simp [hshort, hle]
        omega
      · simp [hshort, hle]

theorem classifyStaticBoolCall_decoded_le_one (success : Bool) (data : Bytes) (word : Nat)
    (hdecoded : classifyStaticBoolCall success data = .decoded word) : word ≤ 1 := by
  obtain ⟨_, _, hle, rfl⟩ := (classifyStaticBoolCall_decoded_iff success data word).mp hdecoded
  exact hle

theorem classifyStaticWordCall_failure (data : Bytes) :
    classifyStaticWordCall false data = .forward data := rfl

theorem classifyStaticWordCall_short (data : Bytes) (hshort : data.length < 32) :
    classifyStaticWordCall true data = .malformed := by
  simp [classifyStaticWordCall, hshort]

theorem classifyStaticWordCall_decoded_iff (success : Bool) (data : Bytes) (word : Nat) :
    classifyStaticWordCall success data = .decoded word ↔
      success = true ∧ 32 ≤ data.length ∧ firstWord data = word := by
  unfold classifyStaticWordCall
  cases success
  · simp
  · by_cases hshort : data.length < 32
    · simp [hshort]
      omega
    · simp [hshort]
      omega

theorem decodeStaticUint256_eq_return_iff_classify (observed : Observation) (word : Nat) :
    decodeStaticUint256 observed = .return word observed.state.frame ↔
      classifyStaticWordCall observed.success observed.state.returndata = .decoded word := by
  rw [classifyStaticWordCall_decoded_iff]
  unfold decodeStaticUint256
  cases hsuccess : observed.success
  · simp
  · by_cases hshort : observed.state.returndata.length < 32
    · simp [hshort]
      omega
    · simp [hshort]
      omega

end Compiler.CompilationModel.DenoteStaticCall
