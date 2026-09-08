/-
  Tests for P-ADDRESS-1 specification.
  Concrete examples and property checks via #eval / #guard.
-/

import PAddress1
open PAddress1

-- § Concrete examples

#guard Address.ofNat? 0 = some Address.zero
#guard (Address.zero.toNat) = 0
#guard Address.ofNat? (ADDR_BOUND - 1) != none
#guard Address.ofNat? ADDR_BOUND = none
#guard Address.ofNat? (ADDR_BOUND + 1) = none

-- § Roundtrip on boundary values

#eval do
  let a0 ← Address.ofNat? 0
  let a1 ← Address.ofNat? 1
  let aMax ← Address.ofNat? (ADDR_BOUND - 1)
  guard (Address.ofNat? a0.toNat = some a0)
  guard (Address.ofNat? a1.toNat = some a1)
  guard (Address.ofNat? aMax.toNat = some aMax)
  return "roundtrip OK"

-- § Injectivity: distinct inputs → distinct addresses

#eval do
  let a42 ← Address.ofNat? 42
  let a43 ← Address.ofNat? 43
  guard (a42 != a43)
  return "injectivity OK"

-- § Batch validation

#guard (validateBatch [0, 1, ADDR_BOUND, 42, ADDR_BOUND + 999]).length = 3

-- § Auth determinism (trivial context)

#eval do
  let ctx : AuthContext := ⟨fun _ _ => Address.ofNat? 7⟩
  let r1 ← ctx.recover 100 200
  let r2 ← ctx.recover 100 200
  guard (r1 = r2)
  return "auth deterministic OK"

-- § Mutation canaries

#guard ADDR_BOUND = 2 ^ 160
#guard ADDR_BOUND > 0

#eval do
  let big ← Address.ofNat? (ADDR_BOUND - 1)
  guard (big.toNat = ADDR_BOUND - 1)
  return "max-address value preserved"
