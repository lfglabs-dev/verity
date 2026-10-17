import Verity.Core.Model.CodeData

open Verity.Core Verity.Core.Model

/- EIP-1014 example 0: deployer=0, salt=0, initcode=0x00.
   Both offsets read the same single zero byte. The independent published
   address distinguishes hashing initcode from treating it as its digest. -/
#eval (show IO Unit from do
  for offset in ([0, 17] : List Nat) do
    let actual := Create2.create2AddressFromMemory (fun _ => Uint256.ofNat 0)
      (Uint256.ofNat offset) (Uint256.ofNat 1) (Uint256.ofNat 0) (Address.ofNat 0)
    if actual.val != 0x4d1a2e2bb4f88f0250f26ffff098b0b30b26bf38 then
      throw (IO.userError s!"EIP-1014 example 0 failed at offset {offset}: {actual.val}")
  IO.println "EIP-1014 example 0: passed at offsets 0 and 17")
