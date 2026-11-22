import Compiler.SolidityImport.StaticOracleMocks
import Compiler.Keccak.Sponge

/-! Explicit `ecrecover` precompile (`address(1)`) program for differential
validation of the imported Solidity `ecrecover` builtin. It follows the EVM
precompile: the input is right-padded to 128 bytes and read as
`(hash, v, r, s)`. A `v` word other than 27 or 28, an `r` or `s` outside
`[1, n)` (high `s` is accepted), an `r` that is not the x-coordinate of a curve
point, or a recovered point at infinity answers with success and empty return
data. Otherwise the answer is the 32-byte left-padded address
`keccak256(x ‖ y)[12:]` of the recovered secp256k1 public key. The response is
computed from the request, never copied from an EVM trace; only `staticcall`s
to `address(1)` are in the program's domain, every other request is an
instrumentation error. Harness code, not a proof assumption: the campaign
compares this program with the EVM's precompile on every observed call.
-/
namespace Compiler.CompilationModel.SolidityImport.PrecompileResponderMocks

open Denote DenoteByteExternalCalls ByteExternalCall

/-- secp256k1 field prime. -/
def fieldPrime : Nat := 2 ^ 256 - 2 ^ 32 - 977

/-- secp256k1 group order. -/
def groupOrder : Nat := 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEBAAEDCE6AF48A03BBFD25E8CD0364141

/-- secp256k1 generator, affine. -/
def generator : Nat × Nat :=
  (0x79BE667EF9DCBBAC55A06295CE870B07029BFCDB2DCE28D959F2815B16F81798,
   0x483ADA7726A3C4655DA4FBFC0E1108A8FD17B448A68554199C47D08FFB10D4B8)

/-- `base ^ exponent % modulus` by square and multiply over the 256 exponent bits. -/
def powMod (base exponent modulus : Nat) : Nat :=
  (List.range 256).reverse.foldl (fun acc bit =>
    let squared := acc * acc % modulus
    if exponent.testBit bit then squared * base % modulus else squared) (1 % modulus)

/-- Field subtraction. -/
def subMod (a b : Nat) : Nat := (a + fieldPrime - b % fieldPrime) % fieldPrime

/-- Jacobian point `(X, Y, Z)`, affine `(X / Z², Y / Z³)`; `Z = 0` is infinity. -/
abbrev Jacobian := Nat × Nat × Nat

/-- Doubling on `y² = x³ + 7`. -/
def double (point : Jacobian) : Jacobian :=
  let (x, y, z) := point
  if z == 0 || y == 0 then (0, 1, 0) else
  let p := fieldPrime
  let a := x * x % p
  let b := y * y % p
  let c := b * b % p
  let d := 2 * subMod (subMod ((x + b) * (x + b) % p) a) c % p
  let e := 3 * a % p
  let x3 := subMod (e * e % p) (2 * d % p)
  let y3 := subMod (e * subMod d x3 % p) (8 * c % p)
  (x3, y3, 2 * y * z % p)

/-- Addition of two Jacobian points. -/
def add (left right : Jacobian) : Jacobian :=
  let (x1, y1, z1) := left
  let (x2, y2, z2) := right
  if z1 == 0 then right else if z2 == 0 then left else
  let p := fieldPrime
  let z1z1 := z1 * z1 % p
  let z2z2 := z2 * z2 % p
  let u1 := x1 * z2z2 % p
  let u2 := x2 * z1z1 % p
  let s1 := y1 * z2 % p * z2z2 % p
  let s2 := y2 * z1 % p * z1z1 % p
  if u1 == u2 then (if s1 == s2 then double left else (0, 1, 0)) else
  let h := subMod u2 u1
  let r := subMod s2 s1
  let hh := h * h % p
  let hhh := hh * h % p
  let v := u1 * hh % p
  let x3 := subMod (subMod (r * r % p) hhh) (2 * v % p)
  let y3 := subMod (r * subMod v x3 % p) (s1 * hhh % p)
  (x3, y3, h * z1 % p * z2 % p)

/-- `k₁·P + k₂·Q` by a joint double-and-add over 256 bits. -/
def mulAdd (k1 : Nat) (p1 : Jacobian) (k2 : Nat) (p2 : Jacobian) : Jacobian :=
  (List.range 256).reverse.foldl (fun acc bit =>
    let acc := double acc
    let acc := if k1.testBit bit then add acc p1 else acc
    if k2.testBit bit then add acc p2 else acc) (0, 1, 0)

/-- Big-endian 32-byte encoding. -/
def wordBytes32 (value : Nat) : List UInt8 :=
  (List.range 32).map fun index => UInt8.ofNat (value / 2 ^ (8 * (31 - index)) % 256)

/-- Big-endian word of the 32 bytes of `input` at `offset`, zero padded. -/
def wordAt (input : Bytes) (offset : Nat) : Nat :=
  (List.range 32).foldl (fun word index => word * 256 + (input.getD (offset + index) 0).toNat) 0

/-- The recovered address, or `none` where the precompile returns no data. -/
def recover (input : Bytes) : Option Nat := do
  let hash := wordAt input 0
  let v := wordAt input 32
  let r := wordAt input 64
  let s := wordAt input 96
  let n := groupOrder
  let p := fieldPrime
  unless (v == 27 || v == 28) && 0 < r && r < n && 0 < s && s < n do none
  let alpha := (r * r % p * r + 7) % p
  let beta := powMod alpha ((p + 1) / 4) p
  unless beta * beta % p == alpha do none
  let y := if beta % 2 == v - 27 then beta else p - beta
  let rInverse := powMod r (n - 2) n
  let u1 := (n - hash % n) % n * rInverse % n
  let u2 := s * rInverse % n
  let (qx, qy, qz) := mulAdd u1 (generator.1, generator.2, 1) u2 (r, y, 1)
  unless qz != 0 do none
  let zInverse := powMod qz (p - 2) p
  let zz := zInverse * zInverse % p
  let x := qx * zz % p
  let y := qy * (zz * zInverse % p) % p
  let digest := KeccakEngine.keccak256 (ByteArray.mk (wordBytes32 x ++ wordBytes32 y).toArray)
  return digest.data.toList.drop 12 |>.foldl (fun acc byte => acc * 256 + byte.toNat) 0

/-- The precompile's answer: success, with the address word or empty data. -/
def respond (request : Request) : Bool × Bytes × List Verity.StorageKey :=
  match recover request.calldata with
  | some address => (true, wordBytes32 address, [])
  | none => (true, [], [])

/-- Only value-free `staticcall`s to `address(1)` are in this program's domain. -/
def environment (gas : Nat) : ByteCallEnvironment :=
  { gas := some gas
    adversary := some { (staticAdversary fun request _ => respond request) with
      accepts := fun request _ =>
        request.kind == .staticcall && request.value == 0 && request.target == 1 } }

private def decimal (value : Lean.Json) : Except String Nat := do
  let text ← value.getStr?
  let some n := text.toNat? | throw "precompile mock expects decimal words"
  unless n < 2^256 do throw "precompile mock word exceeds uint256"
  return n

/-- Parse `ecrecover-precompile-v1`; every other program is configured by
`StaticOracleMocks.configure`. -/
def configure (input : Lean.Json) : Except String ByteCallEnvironment := do
  let config ← input.getObjVal? "byteCallEnvironment"
  let program ← config.getObjValAs? String "program"
  unless program == "ecrecover-precompile-v1" do return ← StaticOracleMocks.configure input
  return environment (← decimal (← config.getObjVal? "gas"))

end Compiler.CompilationModel.SolidityImport.PrecompileResponderMocks
