/-
  Verity.Macro.KeccakString: macro-time Keccak-256 string-literal sugar (#1973)

  Provides the macro expansion for the `keccakString "<literal>"` term form
  declared in `Verity.Macro.Syntax`. The hash is computed at macro
  expansion time and the result is emitted as a `Uint256` numeric literal —
  no runtime hashing, no `native_decide` cost at use sites, no per-author
  copy of the digest.

  The same syntax is also pattern-matched directly by the `verity_contract`
  translator (`Verity.Macro.Translate.Expr`), which materialises the digest
  as a `Compiler.CompilationModel.Expr.literal` inside `constants` /
  `immutable` blocks before the term ever reaches this macro. Outside
  `verity_contract` bodies (e.g. in proofs, smoke tests, helper defs) the
  macro_rule below is what gets invoked.

  Sibling to `Verity.Macro.KeccakLit`, which exposes the same digest as an
  ordinary Lean def (`keccak256_lit` / `keccak256_nat`) for callers that
  need to pass a `String` value (rather than a literal). The two surfaces
  are equivalent on string literals; `keccakString` is preferred because
  it fails closed at parse time on non-literal arguments (EIP-712 type
  hashes, ERC-7201 namespaces, event topic constants, … must always be
  statically known).

  Example:

    constants
      DOMAIN_TYPE_HASH : Uint256 :=
        keccakString "EIP712Domain(string name,string version,uint256 chainId,address verifyingContract)"
      NAME_HASH        : Uint256 := keccakString "ERC4337"
      VERSION_HASH     : Uint256 := keccakString "0.9.0"

  Trust assumptions are unchanged: the digest is computed by the in-tree
  pure `Compiler.Keccak.Sponge` engine (shipped via #1416 / #1683).
-/

import Lean
import Compiler.Keccak.Sponge
import Verity.Core
import Verity.Macro.Syntax

namespace Verity.Macro

open Lean

@[macro keccakStringTerm]
def expandKeccakString : Macro := fun stx => do
  match stx with
  | `(keccakString $s:str) =>
      let raw := s.getString
      let digest : Nat := KeccakEngine.keccak256_str_nat raw
      let digestLit := Syntax.mkNumLit (toString digest)
      `((Verity.Core.Uint256.ofNat $digestLit))
  | _ => Macro.throwUnsupported

end Verity.Macro
