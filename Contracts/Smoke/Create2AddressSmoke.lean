import Contracts.Common
import Compiler.Modules.Create2SSTORE2
import Contracts.ProofKit

namespace Contracts.Smoke

open Contracts
open Verity hiding pure bind
open Verity.EVM.Uint256

-- CREATE2 from a bytes argument: the EDSL returns the EIP-1014 address
-- (`create2Live`), the compiled code deploys there (`test/Create2AddressSmoke.t.sol`).
verity_contract Create2AddressSmoke where
  storage

  function reentrancy_trusted deploy (initcode : Bytes, salt : Uint256) local_obligations [initcode_scratch := assumed "copies the initcode to memory at 0 for create2"] : Address := do
    copyBytes initcode 0
    let size := bytesLength initcode
    let zero := 0
    let pointer ← ecmCall Compiler.Modules.Create2SSTORE2.deployModule
      [zero, zero, size, salt]
    return wordToAddress pointer

open Contracts.ProofKit in
/-- `deploy initcode salt` returns the EIP-1014 address of `this`, `salt` and
`keccak256(initcode)`, for every initcode, salt and state. The concrete EIP-1014 vector is
checked against the compiled code by `test/Create2AddressSmoke.t.sol`. -/
theorem deploy_is_create2Address (initcode : ByteArray) (salt : Uint256) (s : ContractState)
    (hsize : initcode.size + 32 < 2 ^ 256) :
    ∃ s', Create2AddressSmoke.deploy .stub initcode salt s =
      .success (Verity.Core.Model.Create2.create2Address salt
        (Verity.Core.Uint256.ofNat (keccakBytes initcode.data.toList)) s.thisAddress) s' := by
  unfold Create2AddressSmoke.deploy
  obtain ⟨u, s1, h1⟩ : ∃ u s1, Contracts.copyBytes initcode 0 s = .success u s1 :=
    ⟨_, _, copyBytes_run _ _ _⟩
  have ht : s1.thisAddress = s.thisAddress := by rw [copyBytes_ok h1]
  rw [bind_step h1, bind_step (create2Live_eq _ _ _ _ _),
    keccak_after_copyBytes h1 (by simpa using hsize), ht]
  exact ⟨s1, congrArg (ContractResult.success · s1) (wordToAddress_ofNat_val _)⟩

end Contracts.Smoke
