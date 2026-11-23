import Contracts.Common
import Contracts.ProofKit

/-!
Storage frames of ECM crossings (`Contracts.ProofKit.Frames`), on the two shapes contracts use:
a precompile read (`ecrecover`, a one-word answer) and a value-carrying `call` with no result.
-/

namespace Contracts.Smoke

open Contracts Contracts.ProofKit
open Verity hiding pure bind

/-- `ecrecover` returns the adversary's one-word answer at its call site, from a state that keeps
storage. -/
theorem ecrecover_returns_adversary_word
    {adv : Compiler.CompilationModel.DenoteExternalCalls.AdversaryModel}
    {hash v r sig w : Uint256} {s s' : ContractState}
    (h : Contracts.ecmCallWords (Compiler.Modules.Precompiles.ecrecoverModule "signer") adv
      [hash, v, r, sig] 0 s = .success w s') :
    ∃ paid ws, KeepsStorage s paid ∧
      adv.result (ecmSite (Compiler.Modules.Precompiles.ecrecoverModule "signer")
        [hash, v, r, sig]) paid = .success ws ∧
      ws.length = 1 ∧ w = Verity.Core.Uint256.ofNat (ws.headD 0) := by
  obtain ⟨paid, ws, hpaid, hres, hlen, hw, _⟩ := ecmCallTypedWords_success h
  refine ⟨paid, ws, hpaid, hres, hlen, ?_⟩
  rw [hw]
  match ws, hlen with
  | [_], _ => rfl

/-- `ecrecover` is a static call: it keeps storage whatever the adversary does. -/
theorem ecrecover_keepsStorage
    {adv : Compiler.CompilationModel.DenoteExternalCalls.AdversaryModel}
    {hash v r sig w : Uint256} {s s' : ContractState}
    (h : Contracts.ecmCallWords (Compiler.Modules.Precompiles.ecrecoverModule "signer") adv
      [hash, v, r, sig] 0 s = .success w s') :
    KeepsStorage s s' :=
  ecmCallTypedWords_keepsStorage_of_staticcall rfl h

/-- Under `NonInterfering`, a value-carrying `call` keeps this contract's storage. -/
theorem callWithValue_keepsStorage
    {adv : Compiler.CompilationModel.DenoteExternalCalls.AdversaryModel}
    {args : List Uint256} {s s' : ContractState} (hadv : NonInterfering adv)
    (h : Contracts.ecmDoWords Compiler.Modules.Calls.callWithValueModule adv args 0 s =
      .success () s') :
    KeepsStorage s s' :=
  ecmCallTypedWords_keepsStorage hadv h

end Contracts.Smoke
