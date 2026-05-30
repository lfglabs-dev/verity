/-!
# SHA-256 (FIPS 180-4) — kernel-computable engine

A pure-Lean, axiom-free implementation of SHA-256 over `ByteArray`, mirroring the
role of `KeccakEngine.keccak256`: it lets the executable source semantics model the
EVM SHA-256 precompile (address `0x02`) with a *computed* 32-byte digest rather than
an abstract placeholder.

The implementation follows FIPS 180-4 directly (no unrolled circuit is needed — the
state is only eight 32-bit words and the compression is 64 rounds, well within the
kernel's reach). `UInt32` arithmetic wraps modulo `2^32`, matching the spec's
addition-mod-2^32. CI cross-checks this output against the EVM/reference SHA-256
(the same trust discipline used for `KeccakEngine`).
-/

namespace Sha256Engine

/-- Rotate a 32-bit word right by `n` bits (`1 ≤ n ≤ 31`). -/
@[inline] def rotr (x : UInt32) (n : UInt32) : UInt32 :=
  (x >>> n) ||| (x <<< (32 - n))

@[inline] def bigSigma0 (x : UInt32) : UInt32 := rotr x 2 ^^^ rotr x 13 ^^^ rotr x 22
@[inline] def bigSigma1 (x : UInt32) : UInt32 := rotr x 6 ^^^ rotr x 11 ^^^ rotr x 25
@[inline] def smallSigma0 (x : UInt32) : UInt32 := rotr x 7 ^^^ rotr x 18 ^^^ (x >>> 3)
@[inline] def smallSigma1 (x : UInt32) : UInt32 := rotr x 17 ^^^ rotr x 19 ^^^ (x >>> 10)

@[inline] def ch (x y z : UInt32) : UInt32 := (x &&& y) ^^^ ((~~~x) &&& z)
@[inline] def maj (x y z : UInt32) : UInt32 := (x &&& y) ^^^ (x &&& z) ^^^ (y &&& z)

/-- SHA-256 round constants `K[0..63]` (first 32 bits of the fractional parts of the
cube roots of the first 64 primes). -/
def K : Array UInt32 := #[
  0x428a2f98, 0x71374491, 0xb5c0fbcf, 0xe9b5dba5, 0x3956c25b, 0x59f111f1, 0x923f82a4, 0xab1c5ed5,
  0xd807aa98, 0x12835b01, 0x243185be, 0x550c7dc3, 0x72be5d74, 0x80deb1fe, 0x9bdc06a7, 0xc19bf174,
  0xe49b69c1, 0xefbe4786, 0x0fc19dc6, 0x240ca1cc, 0x2de92c6f, 0x4a7484aa, 0x5cb0a9dc, 0x76f988da,
  0x983e5152, 0xa831c66d, 0xb00327c8, 0xbf597fc7, 0xc6e00bf3, 0xd5a79147, 0x06ca6351, 0x14292967,
  0x27b70a85, 0x2e1b2138, 0x4d2c6dfc, 0x53380d13, 0x650a7354, 0x766a0abb, 0x81c2c92e, 0x92722c85,
  0xa2bfe8a1, 0xa81a664b, 0xc24b8b70, 0xc76c51a3, 0xd192e819, 0xd6990624, 0xf40e3585, 0x106aa070,
  0x19a4c116, 0x1e376c08, 0x2748774c, 0x34b0bcb5, 0x391c0cb3, 0x4ed8aa4a, 0x5b9cca4f, 0x682e6ff3,
  0x748f82ee, 0x78a5636f, 0x84c87814, 0x8cc70208, 0x90befffa, 0xa4506ceb, 0xbef9a3f7, 0xc67178f2]

/-- Initial hash value `H^(0)` (first 32 bits of the fractional parts of the square
roots of the first 8 primes). -/
def H0 : Array UInt32 := #[
  0x6a09e667, 0xbb67ae85, 0x3c6ef372, 0xa54ff53a, 0x510e527f, 0x9b05688c, 0x1f83d9ab, 0x5be0cd19]

/-- Read the big-endian 32-bit word at byte `off` of a padded message. -/
@[inline] def wordBE (msg : ByteArray) (off : Nat) : UInt32 :=
  let b0 := (msg[off]?     |>.getD 0).toUInt32
  let b1 := (msg[off + 1]? |>.getD 0).toUInt32
  let b2 := (msg[off + 2]? |>.getD 0).toUInt32
  let b3 := (msg[off + 3]? |>.getD 0).toUInt32
  (b0 <<< 24) ||| (b1 <<< 16) ||| (b2 <<< 8) ||| b3

/-- FIPS 180-4 §5.1.1 padding: append `0x80`, then `0x00` bytes until the length is
`≡ 56 (mod 64)`, then the 64-bit big-endian bit length. -/
def pad (data : ByteArray) : ByteArray :=
  let bitLen : Nat := data.size * 8
  let withOne := data.push 0x80
  let zeros : Nat := (56 + 64 - (withOne.size % 64)) % 64
  let padded := zeros.fold (fun _ _ acc => acc.push 0x00) withOne
  let lenBytes : ByteArray := ⟨(List.range 8).reverse.foldl
    (fun acc i => acc.push (UInt8.ofNat ((bitLen >>> (8 * i)) &&& 0xFF))) #[]⟩
  padded ++ lenBytes

/-- Build the 64-word message schedule `W` for the 64-byte block at `base`. -/
def schedule (msg : ByteArray) (base : Nat) : Array UInt32 := Id.run do
  let mut w : Array UInt32 := Array.replicate 64 0
  for i in [0:16] do
    w := w.set! i (wordBE msg (base + 4 * i))
  for i in [16:64] do
    let s0 := smallSigma0 (w.getD (i - 15) 0)
    let s1 := smallSigma1 (w.getD (i - 2) 0)
    w := w.set! i (w.getD (i - 16) 0 + s0 + w.getD (i - 7) 0 + s1)
  return w

/-- Apply the 64-round compression of one block to the running hash `h`. -/
def compress (h : Array UInt32) (w : Array UInt32) : Array UInt32 := Id.run do
  let mut a := h.getD 0 0
  let mut b := h.getD 1 0
  let mut c := h.getD 2 0
  let mut d := h.getD 3 0
  let mut e := h.getD 4 0
  let mut f := h.getD 5 0
  let mut g := h.getD 6 0
  let mut hh := h.getD 7 0
  for i in [0:64] do
    let t1 := hh + bigSigma1 e + ch e f g + K.getD i 0 + w.getD i 0
    let t2 := bigSigma0 a + maj a b c
    hh := g; g := f; f := e; e := d + t1
    d := c; c := b; b := a; a := t1 + t2
  return #[h.getD 0 0 + a, h.getD 1 0 + b, h.getD 2 0 + c, h.getD 3 0 + d,
           h.getD 4 0 + e, h.getD 5 0 + f, h.getD 6 0 + g, h.getD 7 0 + hh]

/-- Serialize the eight hash words big-endian into the 32-byte digest. -/
def serialize (h : Array UInt32) : ByteArray := Id.run do
  let mut out : ByteArray := ByteArray.empty
  for i in [0:8] do
    let x := h.getD i 0
    out := out.push (UInt8.ofNat ((x >>> 24).toNat &&& 0xFF))
    out := out.push (UInt8.ofNat ((x >>> 16).toNat &&& 0xFF))
    out := out.push (UInt8.ofNat ((x >>> 8).toNat &&& 0xFF))
    out := out.push (UInt8.ofNat (x.toNat &&& 0xFF))
  return out

/-- Compute the SHA-256 digest (32 bytes) of `data`. -/
def sha256 (data : ByteArray) : ByteArray := Id.run do
  let msg := pad data
  let nBlocks := msg.size / 64
  let mut h := H0
  for blk in [0:nBlocks] do
    h := compress h (schedule msg (64 * blk))
  return serialize h

/-- Convert a big-endian `ByteArray` to a `Nat` (byte 0 most significant), matching
`KeccakEngine.byteArrayToNatBE`. -/
def byteArrayToNatBE (ba : ByteArray) : Nat :=
  ba.foldl (fun acc byte => acc * 256 + byte.toNat) 0

/-- SHA-256 digest of `data` as a big-endian 256-bit `Nat`. -/
def sha256_nat (data : ByteArray) : Nat :=
  byteArrayToNatBE (sha256 data)

end Sha256Engine
