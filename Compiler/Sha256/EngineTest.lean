import Compiler.Sha256.Engine

/-!
# SHA-256 engine smoke tests

Reference vectors from FIPS 180-4 / NIST examples. This file is imported by
`Compiler.lean`, so `lake build Compiler` compiles the engine and checks these
kernel-computable examples.
-/

namespace Sha256Engine.Test

private def emptyDigestNat : Nat :=
  0xe3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855

private def abcDigestNat : Nat :=
  0xba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad

example : (sha256 ByteArray.empty).size = 32 := by
  native_decide

example : sha256_nat ByteArray.empty = emptyDigestNat := by
  native_decide

example : sha256_nat "abc".toUTF8 = abcDigestNat := by
  native_decide

end Sha256Engine.Test
