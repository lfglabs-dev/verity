import Compiler.CompilationModel.AbiTypeLayout

/-!
# Fixed-shape ABI literals

An `emit` argument for a composite event parameter may be written as a literal, such as
`[⟨target, action, [sel]⟩]` for `(address,uint8,bytes4[])[]`. Its shape (array lengths, tuple
arity) is fixed at compile time, so every word of its standard ABI encoding (head/tail layout,
offsets and lengths) is a compile-time constant except the leaves.

`abiLitEncode ty lit` is that encoding, as constants and typed leaves. The compiler
(`EventEmission.lean`, leaves are `Expr`s) and the executable EDSL (`Contracts.emitEncoded`,
leaves are words) both use it, so they agree on the logged words by construction.

- For a dynamic `ty` the words are the value's tail (what its head offset points at).
- For a static `ty` they are its inline head words.
- `bytes`/`string` literals are only the empty one (`emptyBytes`): one zero length word.
-/

namespace Compiler.CompilationModel

/-- A literal ABI value of fixed shape. A `composite` is an array's elements, a tuple's or fixed
array's members, or (with no items) the empty `bytes`/`string`. -/
inductive AbiLit (α : Type) where
  | leaf (value : α)
  | composite (items : List (AbiLit α))
  deriving Repr, Inhabited

/-- One word of a literal's encoding: a compile-time constant, or a leaf with its ABI type
(normalized to that type when emitted). -/
inductive AbiWord (α : Type) where
  | const (value : Nat)
  | leaf (ty : ParamType) (value : α)
  deriving Repr

/-- `ty` with newtype wrappers removed (they are erased to their base type in the ABI). -/
def abiLitBaseType : ParamType → ParamType
  | .newtypeOf _ base => abiLitBaseType base
  | ty => ty

/-- Whether a literal leaf may have this ABI type: the one-word value types whose
normalization is a mask (or none). -/
def abiLitLeafType? : ParamType → Bool
  | .uint256 | .int256 | .uint8 | .uint16 | .uintN _ | .bytesN _ | .address | .bytes32 | .bool => true
  | _ => false

/-- Head/tail layout of a sequence of encoded items (`(dynamic?, words)`): the head holds each
static item's words and each dynamic item's byte offset, relative to the sequence start; the
tails follow in order. -/
def abiLitLayoutSeq {α : Type} (items : List (Bool × List (AbiWord α))) : List (AbiWord α) :=
  let headWords := items.foldl (fun n (dyn, ws) => n + if dyn then 1 else ws.length) 0
  let step := fun (acc : List (AbiWord α) × List (AbiWord α) × Nat)
      (item : Bool × List (AbiWord α)) =>
    let (head, tail, tailWords) := acc
    let (dyn, ws) := item
    if dyn then
      (head ++ [.const (32 * (headWords + tailWords))], tail ++ ws, tailWords + ws.length)
    else
      (head ++ ws, tail, tailWords)
  let (head, tail, _) := items.foldl step ([], [], 0)
  head ++ tail

mutual
  /-- The ABI encoding of `lit` at type `ty` (see the module docstring), or why `lit` does not
  have that shape. -/
  def abiLitEncode {α : Type} (ty : ParamType) : AbiLit α → Except String (List (AbiWord α))
    | .leaf value =>
        let base := abiLitBaseType ty
        if abiLitLeafType? base then pure [.leaf base value]
        else throw s!"a single value cannot encode ABI type {repr base}"
    | .composite items =>
        match abiLitBaseType ty with
        | .bytes | .string =>
            if items.isEmpty then pure [.const 0]
            else throw "a bytes/string literal must be empty (emptyBytes)"
        | .array elemTy => do
            let encoded ← abiLitEncodeItems (items.map fun _ => elemTy) items
            pure (.const items.length :: abiLitLayoutSeq encoded)
        | .fixedArray elemTy n =>
            if items.length != n then
              throw s!"fixed array literal has {items.length} items, its type has {n}"
            else do
              pure (abiLitLayoutSeq (← abiLitEncodeItems (items.map fun _ => elemTy) items))
        | .tuple tys =>
            if items.length != tys.length then
              throw s!"tuple literal has {items.length} members, its type has {tys.length}"
            else do
              pure (abiLitLayoutSeq (← abiLitEncodeItems tys items))
        | base => throw s!"a composite literal cannot encode ABI type {repr base}"

  /-- Encode each item at its type, recording whether the type is dynamic. -/
  def abiLitEncodeItems {α : Type} :
      List ParamType → List (AbiLit α) → Except String (List (Bool × List (AbiWord α)))
    | ty :: tys, item :: items => do
        let ws ← abiLitEncode ty item
        let rest ← abiLitEncodeItems tys items
        pure ((isDynamicParamType ty, ws) :: rest)
    | _, _ => pure []
end

/-- A word normalized to an ABI value type, as solc's encoder cleans it: masked to the type's
width (`bytesN` keeps its high bytes), `bool` to 0 or 1. -/
def abiLitNormalizeWord (ty : ParamType) (word : Nat) : Nat :=
  match ty with
  | .uint8 => word % 2 ^ 8
  | .uint16 => word % 2 ^ 16
  | .uintN bits => word % 2 ^ bits
  | .address => word % 2 ^ 160
  | .bytesN bytes => word / 2 ^ (8 * (32 - bytes)) % 2 ^ (8 * bytes) * 2 ^ (8 * (32 - bytes))
  | .bool => if word = 0 then 0 else 1
  | _ => word

/-- The encoded words of a literal with word leaves; `[]` if `lit` does not have `ty`'s shape
(the macro and the compiler reject such literals first). -/
def abiLitWords (ty : ParamType) (lit : AbiLit Nat) : List Nat :=
  match abiLitEncode ty lit with
  | .ok ws => ws.map fun
      | .const n => n
      | .leaf leafTy v => abiLitNormalizeWord leafTy v
  | .error _ => []

mutual
  /-- An `emit` argument as an ABI literal: `Expr.abiLiteral` nodes become `composite`s, any other
  expression is a leaf. -/
  def exprAbiLit : Expr → AbiLit Expr
    | .abiLiteral items => .composite (exprAbiLitList items)
    | e => .leaf e

  def exprAbiLitList : List Expr → List (AbiLit Expr)
    | [] => []
    | e :: es => exprAbiLit e :: exprAbiLitList es
end

end Compiler.CompilationModel
