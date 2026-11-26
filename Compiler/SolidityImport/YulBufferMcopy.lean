import Lean
import Compiler.ECM
import Compiler.SolidityImport.AbiEncoding
import Compiler.SolidityImport.TypesAndRecords

set_option autoImplicit false

/-!
# Yul `mcopy` Between Modelled Byte Buffers (`Compiler.SolidityImport.YulBufferMcopy`)

Construct-generic EIP-5656 (`MCOPY`) lowering and static `Nat` range verification for copies
between byte-addressable memory buffers (`bytes memory` / `string memory`) whose payloads the
importer models in physical byte memory:

* `emitBufferMcopyLoop` lowers `mcopy(dst, src, len)` over two modelled buffers to covered word
  loads and masked word stores: a zero runtime `len` performs no memory reads, writes, or
  expansion; a positive `len` compares the runtime byte start addresses and copies forward when
  `dstStart ≤ srcStart` and backward when `srcStart < dstStart`, giving exact `memmove` semantics
  on arbitrary overlapping or aliased slices while preserving every byte outside `[dst, dst + len)`.
* `unprovedMcopySites` runs a sound forward abstract interpreter over the root's complete lowered
  `Stmt` list (`abiGuards ++ body`), tracking exact non-wrapping `Nat` affine forms, constant
  upper bounds, guarded inequalities, and Floyd ghost-renaming across reassignments and loops,
  rejecting any `mcopy` site whose positive-length source or destination slice is not proved
  bounded by its buffer's modelled byte length (`< 2^128`).
-/

namespace Compiler.CompilationModel.SolidityImport

open Lean (Json RBMap)
open Compiler.CompilationModel

/-- Metadata recorded at a lowered buffer-to-buffer `mcopy` site for whole-root `Stmt` range
verification (`unprovedMcopySites`). Every `String` field names a fresh SSA `.letVar` emitted
immediately before `emitBufferMcopyLoop`, with `srcSizeVar` emitted last as the site trigger. -/
structure McopySite where
  lenVar : String
  dstPtrVar : String
  dstOffVars : List String
  dstLitOff : Nat
  dstSizeVar : String
  srcPtrVar : String
  srcOffVars : List String
  srcLitOff : Nat
  srcSizeVar : String
  node : Json
  file : String
  stack : List Nat

/-- Classification of why a lowered buffer `mcopy` site was rejected after whole-root analysis. -/
inductive McopyFailureKind where
  | unprovedBounds
  | shortStringBuffer
  deriving DecidableEq, Repr

/-- Metadata recorded at a lowered `create2` site over an `initcodeTemplates` byte buffer. -/
structure Create2TemplateSite where
  rootPtrVar : String
  node : Json
  file : String
  stack : List Nat

/-- An un-reassigned Yul `let` variable holding `add(buf, 0x20 + ...)` of a modelled byte buffer.
Its dynamic offset summands are captured into fresh scalar bindings at the `let` declaration so
later `mcopy` uses neither re-evaluate operands nor expose raw heap addresses to scalar Yul. -/
structure YulBufferCursor where
  declId : Nat
  buffer : EncodedBytes
  litOffset : Nat
  offsetVars : List String

/-- Fresh temporary names consumed by `emitBufferMcopyLoop`. -/
structure BufferMcopyTemps where
  dstStart : String
  srcStart : String
  fwdIdx : String
  fwdByte : String
  fwdWord : String
  bwdStep : String
  bwdIdx : String
  bwdByte : String
  bwdWord : String

/-- Build the modulo-`2^256` offset sum `litOff + ∑ vars` (proved non-wrapping when `len > 0`
by `unprovedMcopySites`). -/
def buildMcopyOffsetExpr (litOff : Nat) (vars : List String) : Expr :=
  match litOff, vars with
  | 0, [] => .literal 0
  | n, [] => .literal n
  | 0, v :: vs => vs.foldl (fun acc u => .add acc (.localVar u)) (.localVar v)
  | n, vs => vs.foldl (fun acc u => .add acc (.localVar u)) (.literal n)

/-- Copy one byte from `srcStartVar + idxExpr` to `dstStartVar + idxExpr` using aligned 32-byte
word loads and a single-lane masked store, preserving all other 31 bytes of the target word. -/
private def copySingleBufferByte (srcStartVar dstStartVar : String) (idxExpr : Expr)
    (byteVar wordVar : String) : List Stmt :=
  let rAddr := Expr.add (.localVar srcStartVar) idxExpr
  let wAddr := Expr.add (.localVar dstStartVar) idxExpr
  let rWord := AbiEncoding.byteWordOffset rAddr
  let rShift := Expr.mul (.literal 8) (.sub (.literal 31) (AbiEncoding.byteLane rAddr))
  let wShift := Expr.mul (.literal 8) (.sub (.literal 31) (AbiEncoding.byteLane wAddr))
  let wMask := Expr.shl wShift (.literal 0xff)
  [ .letVar byteVar (.bitAnd (.shr rShift (.mload rWord)) (.literal 0xff))
  , .letVar wordVar (AbiEncoding.byteWordOffset wAddr)
  , .mstore (.localVar wordVar)
      (.bitOr (.bitAnd (.mload (.localVar wordVar)) (.bitNot wMask))
        (.shl wShift (.localVar byteVar))) ]

/-- Emit exact EIP-5656 `mcopy` statements between two modelled byte-buffer payloads:
zero length does nothing; positive length copies forward when `dstStart ≤ srcStart` and backward
when `srcStart < dstStart` (`memmove` semantics on overlap). -/
def emitBufferMcopyLoop (dstBase dstOff srcBase srcOff : Expr) (lenVar : String)
    (temps : BufferMcopyTemps) : Stmt :=
  let forwardLoop := Stmt.forEach temps.fwdIdx (.localVar lenVar)
    (copySingleBufferByte temps.srcStart temps.dstStart (.localVar temps.fwdIdx)
      temps.fwdByte temps.fwdWord)
  let backwardIdx := Stmt.letVar temps.bwdIdx
    (.sub (.sub (.localVar lenVar) (.literal 1)) (.localVar temps.bwdStep))
  let backwardLoop := Stmt.forEach temps.bwdStep (.localVar lenVar)
    (backwardIdx :: copySingleBufferByte temps.srcStart temps.dstStart
      (.localVar temps.bwdIdx) temps.bwdByte temps.bwdWord)
  .ite (.eq (.localVar lenVar) (.literal 0)) []
    [ .letVar temps.dstStart (.add dstBase dstOff)
    , .letVar temps.srcStart (.add srcBase srcOff)
    , .ite (.le (.localVar temps.dstStart) (.localVar temps.srcStart))
        [forwardLoop]
        [backwardLoop] ]

/-- Typed variable identifier in the `Nat` bounds domain: either a current program scalar binding
or a fresh ghost snapshot of a reassigned/havoced binding's pre-state value. -/
inductive VarKey where
  | prog (name : String)
  | ghost (id : Nat)
  deriving DecidableEq, Repr

instance : Ord VarKey where
  compare
    | .prog a, .prog b => compare a b
    | .prog _, .ghost _ => .lt
    | .ghost _, .prog _ => .gt
    | .ghost a, .ghost b => compare a b

/-- Non-negative affine expression `const + ∑ coeff_i * key_i` over `Uint256` scalar values in
exact `Nat` arithmetic (never modulo `2^256`). -/
structure AffineNat where
  const : Nat := 0
  terms : List (VarKey × Nat) := []
  deriving DecidableEq, Repr, Inhabited

/-- Exact natural cancellation behind single-step and summed inequality discharge:
if `p ≤ q` and `lhs + q ≤ rhs + p` in `Nat`, then `lhs ≤ rhs`. -/
theorem nat_le_of_add_le_add {lhs rhs p q : Nat}
    (hpq : p ≤ q) (h : lhs + q ≤ rhs + p) : lhs ≤ rhs := by
  omega

namespace AffineNat

def ofConst (c : Nat) : AffineNat := { const := c, terms := [] }

def ofVarScaled (k : VarKey) (c : Nat) : AffineNat :=
  if c == 0 then { const := 0, terms := [] } else { const := 0, terms := [(k, c)] }

def ofVar (k : VarKey) : AffineNat := ofVarScaled k 1

private def mergeTerms : List (VarKey × Nat) → List (VarKey × Nat) → List (VarKey × Nat)
  | [], ys => ys
  | xs, [] => xs
  | (kx, cx) :: xs, (ky, cy) :: ys =>
      match compare kx ky with
      | .lt => (kx, cx) :: mergeTerms xs ((ky, cy) :: ys)
      | .gt => (ky, cy) :: mergeTerms ((kx, cx) :: xs) ys
      | .eq =>
          let s := cx + cy
          if s == 0 then mergeTerms xs ys else (kx, s) :: mergeTerms xs ys

def add (a b : AffineNat) : AffineNat :=
  { const := a.const + b.const, terms := mergeTerms a.terms b.terms }

def scale (k : Nat) (a : AffineNat) : AffineNat :=
  if k == 0 then ofConst 0
  else { const := k * a.const, terms := a.terms.map fun (v, c) => (v, k * c) }

def coeffOf (a : AffineNat) (k : VarKey) : Nat :=
  match a.terms.find? (·.1 == k) with
  | some (_, c) => c
  | none => 0

def mentions (a : AffineNat) (k : VarKey) : Bool :=
  a.terms.any (·.1 == k)

/-- Exact coefficient-wise difference `a - b` when `b` is dominated term-by-term by `a`. -/
def sub? (a b : AffineNat) : Option AffineNat := do
  guard (b.const ≤ a.const)
  guard (b.terms.all fun (k, cb) => cb ≤ a.coeffOf k)
  let remTerms := a.terms.filterMap fun (k, ca) =>
    let cb := b.coeffOf k
    if ca == cb then none else some (k, ca - cb)
  some { const := a.const - b.const, terms := remTerms }

def renameKey (oldKey newKey : VarKey) (a : AffineNat) : AffineNat :=
  if !a.mentions oldKey then a
  else
    let base : AffineNat := { const := a.const, terms := a.terms.filter (·.1 != oldKey) }
    base.add (ofVarScaled newKey (a.coeffOf oldKey))

end AffineNat

private def maxWordVal : Nat := 2 ^ 256 - 1
private def maxAllocVal : Nat := 2 ^ 64 - 1

/-- Atomic facts carried by boolean locals and guard conditions. -/
private inductive AtomFact where
  | leq (lhs rhs : AffineNat)
  | eq (lhs rhs : AffineNat)
  deriving DecidableEq, Repr

private def AtomFact.renameKey (oldKey newKey : VarKey) : AtomFact → AtomFact
  | .leq l r => .leq (l.renameKey oldKey newKey) (r.renameKey oldKey newKey)
  | .eq l r => .eq (l.renameKey oldKey newKey) (r.renameKey oldKey newKey)

/-- Abstract domain state for forward `Stmt` bounds verification. -/
private structure AbsState where
  unreachable : Bool := false
  nextGhost : Nat := 0
  defs : RBMap VarKey AffineNat compare := RBMap.empty
  upper : RBMap VarKey Nat compare := RBMap.empty
  leqs : Array (AffineNat × AffineNat) := #[]
  eqs : Array (AffineNat × AffineNat) := #[]
  boolTrue : RBMap VarKey (List AtomFact) compare := RBMap.empty
  boolFalse : RBMap VarKey (List AtomFact) compare := RBMap.empty
  reserveEnds : RBMap String (String × Expr) compare := RBMap.empty
  extCodeArrays : Array String := #[]

private def expandAff (st : AbsState) (a : AffineNat) : AffineNat :=
  a.terms.foldl
    (fun acc (k, c) =>
      match st.defs.find? k with
      | some d => acc.add (d.scale c)
      | none => acc.add (.ofVarScaled k c))
    (AffineNat.ofConst a.const)

private def rewriteEqs (st : AbsState) (a : AffineNat) : AffineNat := Id.run do
  let mut cur := expandAff st a
  for _ in [:st.eqs.size] do
    let mut changed := false
    for (lhs, rhs) in st.eqs do
      let lhs := expandAff st lhs
      let rhs := expandAff st rhs
      -- Orient `rhs = 1 * v` (with `v` not in `lhs`), e.g. `dest + 54 = compValue_len`.
      if rhs.const == 0 then
        if let [(v, 1)] := rhs.terms then
          if !lhs.mentions v && cur.mentions v then
            let c := cur.coeffOf v
            let stripped : AffineNat := { const := cur.const, terms := cur.terms.filter (·.1 != v) }
            cur := stripped.add (lhs.scale c)
            changed := true
      if lhs.const == 0 then
        if let [(v, 1)] := lhs.terms then
          if !rhs.mentions v && cur.mentions v then
            let c := cur.coeffOf v
            let stripped : AffineNat := { const := cur.const, terms := cur.terms.filter (·.1 != v) }
            cur := stripped.add (rhs.scale c)
            changed := true
    unless changed do break
  return cur

private def lookupKeyUpper (st : AbsState) (k : VarKey) : Nat :=
  st.upper.find? k |>.getD maxWordVal

private def affineUpper (st : AbsState) (a : AffineNat) : Nat :=
  let expanded := expandAff st a
  expanded.terms.foldl (fun acc (k, c) => acc + c * lookupKeyUpper st k) expanded.const

private def affineLower (st : AbsState) (a : AffineNat) : Nat := Id.run do
  let norm := rewriteEqs st a
  let mut best := norm.const
  for (p, q) in st.leqs do
    let pNorm := rewriteEqs st p
    let qNorm := rewriteEqs st q
    if let some rem := norm.sub? qNorm then
      best := max best (pNorm.const + rem.const)
  return best

/-- Sound upper bound of a runtime `Expr` (`≤ 2^256 - 1`). -/
private partial def evalUpper (st : AbsState) : Expr → Nat
  | .literal n => if n < 2 ^ 256 then n else n % 2 ^ 256
  | .localVar v | .param v =>
      min (lookupKeyUpper st (.prog v)) (min (affineUpper st (.ofVar (.prog v))) maxWordVal)
  | .mload (.localVar arr) =>
      if st.extCodeArrays.contains arr then maxAllocVal else maxWordVal
  | .bitAnd a b => min (evalUpper st a) (evalUpper st b)
  | .mod _ (.literal m) => if 0 < m && m ≤ 2 ^ 256 then m - 1 else maxWordVal
  | .div a (.literal d) => if 0 < d && d < 2 ^ 256 then evalUpper st a / d else maxWordVal
  | .shr (.literal s) a =>
      let s' := s % 2 ^ 256
      if s' < 256 then evalUpper st a / 2 ^ s' else 0
  | .lt _ _ | .le _ _ | .gt _ _ | .ge _ _ | .eq _ _
  | .slt _ _ | .sgt _ _ | .logicalNot _ | .logicalAnd _ _ | .logicalOr _ _ => 1
  | .add a b =>
      let u := evalUpper st a + evalUpper st b
      if u < 2 ^ 256 then u else maxWordVal
  | .mul a b =>
      let u := evalUpper st a * evalUpper st b
      if u < 2 ^ 256 then u else maxWordVal
  | _ => maxWordVal

/-- Discharge `lhs0 ≤ rhs0` in exact `Nat` from `st`'s definitions, equalities, bounds, and
inequalities (`nat_le_of_add_le_add`). -/
private def proveLeq (st : AbsState) (lhs0 rhs0 : AffineNat) : Bool := Id.run do
  if st.unreachable then return true
  let lhs := rewriteEqs st lhs0
  let rhs := rewriteEqs st rhs0
  if (rhs.sub? lhs).isSome then return true
  if affineUpper st lhs ≤ affineLower st rhs then return true
  -- Replace any variable in `lhs` that has no match in `rhs` or `leqs` when bounded, or build
  -- a tightened upper approximation freeing bounded slack terms.
  let normLeqs := st.leqs.map fun (p, q) => (rewriteEqs st p, rewriteEqs st q)
  for (p, q) in normLeqs do
    if ((rhs.add p).sub? (lhs.add q)).isSome then return true
    -- Positive scaling `k * p ≤ k * q` for strided loop bounds (`32 * (i + 1) ≤ 32 * count`).
    for (v, coeff) in lhs.terms do
      if coeff > 1 && p.coeffOf v == 1 then
        let ps := p.scale coeff
        let qs := q.scale coeff
        if ((rhs.add ps).sub? (lhs.add qs)).isSome then return true
    -- Substitute known finite upper bounds on `lhs` variables absent from `p`.
    let lhsCapped := lhs.terms.foldl
      (fun acc (v, c) =>
        let u := lookupKeyUpper st v
        if !p.mentions v && !rhs.mentions v && u < maxAllocVal then
          acc.add (.ofConst (c * u))
        else acc.add (.ofVarScaled v c))
      (AffineNat.ofConst lhs.const)
    if ((rhs.add p).sub? (lhsCapped.add q)).isSome then return true
  if normLeqs.size ≤ 64 then
    for i in [:normLeqs.size] do
      let (p1, q1) := normLeqs[i]!
      for j in [i:normLeqs.size] do
        let (p2, q2) := normLeqs[j]!
        let p := p1.add p2
        let q := q1.add q2
        if ((rhs.add p).sub? (lhs.add q)).isSome then return true
  return false

/-- Exact `Nat` affine representation of `e`, returning `none` whenever evaluation could wrap
modulo `2^256`. -/
private partial def affExact? (st : AbsState) : Expr → Option AffineNat
  | .literal n => if n < 2 ^ 256 then some (.ofConst n) else none
  | .localVar v | .param v => some (expandAff st (.ofVar (.prog v)))
  | .add a b => do
      guard (evalUpper st a + evalUpper st b < 2 ^ 256)
      return (← affExact? st a).add (← affExact? st b)
  | .sub a b => do
      let affA ← affExact? st a
      let affB ← affExact? st b
      guard (proveLeq st affB affA)
      affA.sub? affB
  | .mul a b =>
      match a, b with
      | .literal 0, _ | _, .literal 0 => some (.ofConst 0)
      | .literal k, other | other, .literal k => do
          guard (k < 2 ^ 256 && k * evalUpper st other < 2 ^ 256)
          return (← affExact? st other).scale k
      | _, _ => none
  | _ => none

/-- Extract the underlying size local from an `AbiEncoding.reserve` size expression when present. -/
private def reserveBoundedSizeVar? : Expr → Option String
  | .localVar s | .param s => some s
  | .bitAnd (.add (.localVar s) (.literal 31)) (.bitNot (.literal 31)) => some s
  | .mul (.div (.add (.localVar s) (.literal 31)) (.literal 32)) (.literal 32) => some s
  | .mul (.literal 32) (.div (.add (.localVar s) (.literal 31)) (.literal 32)) => some s
  | _ => none

/-- Rename `.prog name` to a fresh `.ghost id` across all facts in `st` (Floyd's assignment /
havoc rule), preserving pre-state relationships without polluting the post-state variable. -/
private def ghostHavoc (name : String) (st : AbsState) : AbsState × VarKey :=
  let oldKey := VarKey.prog name
  let gKey := VarKey.ghost st.nextGhost
  let nextDefs := st.defs.fold (init := RBMap.empty) fun acc k v =>
    let k' := if k == oldKey then gKey else k
    acc.insert k' (v.renameKey oldKey gKey)
  let nextUpper := st.upper.fold (init := RBMap.empty) fun acc k u =>
    acc.insert (if k == oldKey then gKey else k) u
  let nextBoolTrue := st.boolTrue.fold (init := RBMap.empty) fun acc k fs =>
    if k == oldKey then acc else acc.insert k (fs.map (·.renameKey oldKey gKey))
  let nextBoolFalse := st.boolFalse.fold (init := RBMap.empty) fun acc k fs =>
    if k == oldKey then acc else acc.insert k (fs.map (·.renameKey oldKey gKey))
  let nextReserve := st.reserveEnds.fold (init := RBMap.empty) fun acc endVar (baseVar, sz) =>
    if endVar == name || baseVar == name || reserveBoundedSizeVar? sz == some name then acc
    else acc.insert endVar (baseVar, sz)
  ( { st with
        nextGhost := st.nextGhost + 1
        defs := nextDefs
        upper := nextUpper
        leqs := st.leqs.map fun (l, r) => (l.renameKey oldKey gKey, r.renameKey oldKey gKey)
        eqs := st.eqs.map fun (l, r) => (l.renameKey oldKey gKey, r.renameKey oldKey gKey)
        boolTrue := nextBoolTrue
        boolFalse := nextBoolFalse
        reserveEnds := nextReserve
        extCodeArrays := st.extCodeArrays.filter (· != name) },
    gKey )

private def havocMany (names : List String) (st : AbsState) : AbsState :=
  names.foldl (fun cur n => (ghostHavoc n cur).1) st

private def applyLeqFact (st : AbsState) (lhs0 rhs0 : AffineNat) : AbsState :=
  if st.unreachable then st else
  let lhs := expandAff st lhs0
  let rhs := expandAff st rhs0
  if rhs.terms.isEmpty then
    if rhs.const < lhs.const then
      { st with unreachable := true }
    else
      let rem := rhs.const - lhs.const
      let nextUpper := lhs.terms.foldl
        (fun acc (k, c) =>
          if c == 0 then acc
          else acc.insert k (min (acc.find? k |>.getD maxWordVal) (rem / c)))
        st.upper
      { st with upper := nextUpper, leqs := st.leqs.push (lhs, rhs) }
  else
    { st with leqs := st.leqs.push (lhs, rhs) }

private def applyFact (st : AbsState) (f : AtomFact) : AbsState :=
  if st.unreachable then st else
  match f with
  | .leq lhs0 rhs0 => applyLeqFact st lhs0 rhs0
  | .eq lhs0 rhs0 =>
      let lhs := expandAff st lhs0
      let rhs := expandAff st rhs0
      if lhs.terms.isEmpty && rhs.terms.isEmpty && lhs.const != rhs.const then
        { st with unreachable := true }
      else
        let st1 := applyLeqFact st lhs rhs
        let st2 := applyLeqFact st1 rhs lhs
        { st2 with eqs := st2.eqs.push (lhs, rhs) }

private def applyFacts (st : AbsState) (fs : List AtomFact) : AbsState :=
  fs.foldl applyFact st

/-- Extract atomic `Nat` facts implied when `cond` evaluates to nonzero (`truth = true`) or
zero (`truth = false`). -/
private partial def extractCond (st : AbsState) (truth : Bool) : Expr → List AtomFact
  | .literal n =>
      let holds := if truth then n % 2 ^ 256 != 0 else n % 2 ^ 256 == 0
      if holds then [] else [.leq (.ofConst 1) (.ofConst 0)]
  | .localVar v | .param v =>
      let key := VarKey.prog v
      let stored := if truth then st.boolTrue.find? key |>.getD []
        else st.boolFalse.find? key |>.getD []
      let nonZeroFact :=
        if truth then [AtomFact.leq (.ofConst 1) (expandAff st (.ofVar key))]
        else [AtomFact.eq (expandAff st (.ofVar key)) (.ofConst 0)]
      stored ++ nonZeroFact
  | .logicalNot inner => extractCond st (!truth) inner
  | .logicalAnd a b =>
      if truth then extractCond st true a ++ extractCond st true b else []
  | .logicalOr a b =>
      if !truth then extractCond st false a ++ extractCond st false b else []
  | .le a b =>
      match affExact? st a, affExact? st b with
      | some la, some lb =>
          if truth then [.leq la lb] else [.leq (lb.add (.ofConst 1)) la]
      | _, _ => []
  | .lt a b =>
      match affExact? st a, affExact? st b with
      | some la, some lb =>
          if truth then [.leq (la.add (.ofConst 1)) lb] else [.leq lb la]
      | _, _ => []
  | .ge a b =>
      match affExact? st a, affExact? st b with
      | some la, some lb =>
          if truth then [.leq lb la] else [.leq (la.add (.ofConst 1)) lb]
      | _, _ => []
  | .gt a b =>
      match affExact? st a, affExact? st b with
      | some la, some lb =>
          if truth then [.leq (lb.add (.ofConst 1)) la] else [.leq la lb]
      | _, _ => []
  | .eq a (.literal 0) => extractCond st (!truth) a
  | .eq (.literal 0) b => extractCond st (!truth) b
  | .eq a b =>
      match affExact? st a, affExact? st b with
      | some la, some lb => if truth then [.eq la lb] else []
      | _, _ => []
  | _ => []

/-- Variables assigned anywhere inside `s` (used to havoc loop-carried and merged branch writes). -/
private partial def stmtAssignedNames : Stmt → List String
  | .letVar name _ | .assignVar name _ => [name]
  | .ite _ yes no => yes.flatMap stmtAssignedNames ++ no.flatMap stmtAssignedNames
  | .forEach varName _ body | .forEachSetBit varName _ body
  | .forEachWhile varName _ _ body => varName :: body.flatMap stmtAssignedNames
  | .internalCallAssign names _ _ | .externalCallBind names _ _ => names
  | .tryExternalCallBind successVar resultVars _ _ => successVar :: resultVars
  | .ecm mod _ => mod.resultVars
  | .unsafeBlock _ body => body.flatMap stmtAssignedNames
  | .matchAdt _ _ branches =>
      branches.flatMap fun (_, vars, body) => vars ++ body.flatMap stmtAssignedNames
  | _ => []

/-- Pre-existing variables mutated inside `s` (excluding fresh `.letVar` temporaries). -/
private partial def stmtMutatedNames : Stmt → List String
  | .assignVar name _ => [name]
  | .ite _ yes no => yes.flatMap stmtMutatedNames ++ no.flatMap stmtMutatedNames
  | .forEach varName _ body | .forEachSetBit varName _ body
  | .forEachWhile varName _ _ body => varName :: body.flatMap stmtAssignedNames
  | .internalCallAssign names _ _ | .externalCallBind names _ _ => names
  | .tryExternalCallBind successVar resultVars _ _ => successVar :: resultVars
  | .ecm mod _ => mod.resultVars
  | .unsafeBlock _ body => body.flatMap stmtMutatedNames
  | .matchAdt _ _ branches =>
      branches.flatMap fun (_, vars, body) => vars ++ body.flatMap stmtAssignedNames
  | _ => []

/-- Whether `aff` references any `.prog v` for `v ∈ names`. -/
private def affMentionsProgAny (names : List String) (aff : AffineNat) : Bool :=
  aff.terms.any fun (k, _) => match k with
    | .prog v => names.contains v
    | .ghost _ => false

/-- Whether `f` references any `.prog v` for `v ∈ names`. -/
private def factMentionsProgAny (names : List String) : AtomFact → Bool
  | .leq l r | .eq l r => affMentionsProgAny names l || affMentionsProgAny names r

/-- Whether `Expr` mentions any local/param variable in `vars`. -/
private def exprMentionsAny (vars : List String) (e : Expr) : Bool :=
  e.anyDeep fun
    | .localVar v | .param v => vars.contains v
    | _ => false

/-- Collect every `(lhs, rhs)` binding or assignment edge anywhere inside `s` (flow-insensitive,
covering loop back-edges, branches, and helper rebindings). -/
private partial def collectAssignEdges : Stmt → List (String × Expr)
  | .letVar lhs rhs | .assignVar lhs rhs => [(lhs, rhs)]
  | .ite _ yes no => yes.flatMap collectAssignEdges ++ no.flatMap collectAssignEdges
  | .forEach _ _ body | .forEachSetBit _ _ body | .forEachWhile _ _ _ body
  | .unsafeBlock _ body => body.flatMap collectAssignEdges
  | .matchAdt _ _ branches => branches.flatMap fun (_, _, body) => body.flatMap collectAssignEdges
  | _ => []

/-- Whole-root fixpoint closure of variables that may hold a pointer derived from `seeds`. -/
private def computePtrTaint (stmts : List Stmt) (seeds : Array String) : List String :=
  if seeds.isEmpty then [] else
  let edges := stmts.flatMap collectAssignEdges
  (List.range (edges.length + 1)).foldl
    (fun tainted _ =>
      edges.foldl
        (fun acc (lhs, rhs) =>
          if acc.contains lhs || !exprMentionsAny acc rhs then acc else lhs :: acc)
        tainted)
    seeds.toList

/-- Verify a single `McopySite` at the program point immediately after its SSA trigger binding. -/
private def siteProvenAt (st : AbsState) (site : McopySite) : Bool :=
  if st.unreachable then true
  else if proveLeq st (.ofVar (.prog site.lenVar)) (.ofConst 0) then true
  else
    let stPos := applyFact st (.leq (.ofConst 1) (expandAff st (.ofVar (.prog site.lenVar))))
    if stPos.unreachable then true
    else
      let lenAff := expandAff stPos (.ofVar (.prog site.lenVar))
      let dstOffAff := site.dstOffVars.foldl
        (fun acc v => acc.add (expandAff stPos (.ofVar (.prog v))))
        (AffineNat.ofConst site.dstLitOff)
      let srcOffAff := site.srcOffVars.foldl
        (fun acc v => acc.add (expandAff stPos (.ofVar (.prog v))))
        (AffineNat.ofConst site.srcLitOff)
      let dstSizeAff := expandAff stPos (.ofVar (.prog site.dstSizeVar))
      let srcSizeAff := expandAff stPos (.ofVar (.prog site.srcSizeVar))
      evalUpper stPos (.localVar site.dstSizeVar) < 2 ^ 128 &&
        evalUpper stPos (.localVar site.srcSizeVar) < 2 ^ 128 &&
        proveLeq stPos (dstOffAff.add lenAff) dstSizeAff &&
        proveLeq stPos (srcOffAff.add lenAff) srcSizeAff

/-- Structural equality on scalar `Expr` trees used in `checkedAdd`, `checkedSub`, `checkedMul`,
and lowered short-circuit `&&` / `||` pattern matching. -/
private partial def exprStructEq : Expr → Expr → Bool
  | .literal a, .literal b => a == b
  | .localVar a, .localVar b | .param a, .param b | .immutable a, .immutable b
  | .storage a, .storage b | .arrayLength a, .arrayLength b
  | .memoryArrayLength a, .memoryArrayLength b
  | .storageArrayLength a, .storageArrayLength b => a == b
  | .caller, .caller | .contractAddress, .contractAddress | .txOrigin, .txOrigin
  | .chainid, .chainid | .msgValue, .msgValue | .selfBalance, .selfBalance
  | .blockTimestamp, .blockTimestamp | .blockNumber, .blockNumber | .blobbasefee, .blobbasefee
  | .baseFee, .baseFee | .gasPrice, .gasPrice | .calldatasize, .calldatasize
  | .returndataSize, .returndataSize => true
  | .mload a, .mload b | .tload a, .tload b | .calldataload a, .calldataload b
  | .extcodesize a, .extcodesize b | .returndataOptionalBoolAt a, .returndataOptionalBoolAt b
  | .bitNot a, .bitNot b | .logicalNot a, .logicalNot b => exprStructEq a b
  | .add a1 a2, .add b1 b2 | .sub a1 a2, .sub b1 b2 | .mul a1 a2, .mul b1 b2
  | .div a1 a2, .div b1 b2 | .sdiv a1 a2, .sdiv b1 b2
  | .mod a1 a2, .mod b1 b2 | .smod a1 a2, .smod b1 b2
  | .bitAnd a1 a2, .bitAnd b1 b2 | .bitOr a1 a2, .bitOr b1 b2
  | .bitXor a1 a2, .bitXor b1 b2 | .shl a1 a2, .shl b1 b2 | .shr a1 a2, .shr b1 b2
  | .sar a1 a2, .sar b1 b2 | .byte a1 a2, .byte b1 b2 | .signextend a1 a2, .signextend b1 b2
  | .keccak256 a1 a2, .keccak256 b1 b2
  | .eq a1 a2, .eq b1 b2 | .ge a1 a2, .ge b1 b2 | .gt a1 a2, .gt b1 b2
  | .sgt a1 a2, .sgt b1 b2 | .lt a1 a2, .lt b1 b2 | .slt a1 a2, .slt b1 b2
  | .le a1 a2, .le b1 b2 | .logicalAnd a1 a2, .logicalAnd b1 b2
  | .logicalOr a1 a2, .logicalOr b1 b2 | .ceilDiv a1 a2, .ceilDiv b1 b2
  | .wMulDown a1 a2, .wMulDown b1 b2 | .wDivUp a1 a2, .wDivUp b1 b2 =>
      exprStructEq a1 b1 && exprStructEq a2 b2
  | _, _ => false

/-- Extract `(dest, prod)` from `checkedMul`'s inner `ok` / narrow-bound branch. -/
private def checkedMulDest? : List Stmt → Option (String × Expr)
  | [.assignVar dest prod] => some (dest, prod)
  | [.ite (.lt (.literal _) _) [.panicCode _] [.assignVar dest prod]] => some (dest, prod)
  | _ => none

mutual
  private partial def stepStmt (st : AbsState) (s : Stmt) (sites : Array McopySite) :
      AbsState × Array McopySite :=
    if st.unreachable then (st, #[]) else
    match s with
    | .letVar name val =>
        let u := evalUpper st val
        let aff? := affExact? st val
        let tFacts := extractCond st true val
        let fFacts := extractCond st false val
        let (st1, gKey) := ghostHavoc name st
        let key := VarKey.prog name
        let st2 :=
          { st1 with
              upper := if u < maxWordVal then st1.upper.insert key u else st1.upper
              defs := match aff? with
                | some aff => st1.defs.insert key (aff.renameKey key gKey)
                | none => st1.defs
              boolTrue := if tFacts.isEmpty then st1.boolTrue
                else st1.boolTrue.insert key (tFacts.map (·.renameKey key gKey))
              boolFalse := if fFacts.isEmpty then st1.boolFalse
                else st1.boolFalse.insert key (fFacts.map (·.renameKey key gKey))
              reserveEnds := match val with
                | .add (.localVar baseVar) sz =>
                    if baseVar != name then st1.reserveEnds.insert name (baseVar, sz)
                    else st1.reserveEnds
                | _ => st1.reserveEnds }
        let failed := sites.filter fun site => site.srcSizeVar == name && !siteProvenAt st2 site
        (st2, failed)
    | .assignVar name val =>
        let u := evalUpper st val
        let aff? := affExact? st val
        let tFacts := extractCond st true val
        let fFacts := extractCond st false val
        let (st1, gKey) := ghostHavoc name st
        let key := VarKey.prog name
        let st2 :=
          { st1 with
              upper := if u < maxWordVal then st1.upper.insert key u else st1.upper
              defs := match aff? with
                | some aff => st1.defs.insert key (aff.renameKey key gKey)
                | none => st1.defs
              boolTrue := if tFacts.isEmpty then st1.boolTrue
                else st1.boolTrue.insert key (tFacts.map (·.renameKey key gKey))
              boolFalse := if fFacts.isEmpty then st1.boolFalse
                else st1.boolFalse.insert key (fFacts.map (·.renameKey key gKey)) }
        (st2, #[])
    | .require cond _ | .requireError cond _ _ =>
        (applyFacts st (extractCond st true cond), #[])
    | .revertEmpty | .revertReturndata | .revertMemory _ _ | .revertError _ _
    | .panicCode _ | .panic _ | .return _ | .returnValues _ | .returnArray _
    | .returnBytes _ | .returnStorageWords _ | .returnCodeData _ | .stop =>
        ({ st with unreachable := true }, #[])
    | .ecm mod _ =>
        if mod == Compiler.ECM.SolidityReturnMemory.module ||
            mod == Compiler.ECM.SolidityRevertMemory.module then
          ({ st with unreachable := true }, #[])
        else
          let st1 := havocMany mod.resultVars st
          let st2 := match mod.resultVars with
            | [r] =>
                if mod == Compiler.ECM.SolidityExtCodeCopy.module r then
                  { st1 with extCodeArrays := st1.extCodeArrays.push r }
                else st1
            | _ => st1
          (st2, #[])
    | .internalCallAssign names _ _ | .externalCallBind names _ _ =>
        (havocMany names st, #[])
    | .tryExternalCallBind successVar resultVars _ _ =>
        (havocMany (successVar :: resultVars) st, #[])
    | .forEach varName count body | .forEachWhile varName count _ body =>
        let countUpper := evalUpper st count
        let countAff? := affExact? st count
        let modVars := (varName :: body.flatMap stmtAssignedNames).eraseDups
        let (stHavoced, countAffRenamed?) :=
          modVars.foldl
            (fun (cur, cAff?) v =>
              let (nxt, gKey) := ghostHavoc v cur
              (nxt, cAff?.map (·.renameKey (.prog v) gKey)))
            (st, countAff?)
        let stBody0 :=
          if countUpper > 0 && countUpper ≤ maxWordVal then
            { stHavoced with upper := stHavoced.upper.insert (.prog varName) (countUpper - 1) }
          else stHavoced
        let stBody := match countAffRenamed? with
          | some cAff =>
              applyFact stBody0 (.leq ((AffineNat.ofVar (.prog varName)).add (.ofConst 1)) cAff)
          | none => stBody0
        let (_, failedBody) := stepList stBody body sites
        (stHavoced, failedBody)
    | .forEachSetBit varName _ body =>
        let modVars := (varName :: body.flatMap stmtAssignedNames).eraseDups
        let stHavoced := havocMany modVars st
        let stBody := { stHavoced with upper := stHavoced.upper.insert (.prog varName) 255 }
        let (_, failedBody) := stepList stBody body sites
        (stHavoced, failedBody)
    | .unsafeBlock _ body =>
        stepList st body sites
    | .matchAdt _ _ branches =>
        let (allFailed, assigned) := branches.foldl
          (fun (accFailed, accAssigned) (_, vars, body) =>
            let (_, fb) := stepList (havocMany vars st) body sites
            (accFailed ++ fb, accAssigned ++ vars ++ body.flatMap stmtAssignedNames))
          (#[], [])
        (havocMany assigned.eraseDups st, allFailed)
    | .ite cond thenB elseB => Id.run do
        let stTrueIn := applyFacts st (extractCond st true cond)
        let stFalseIn := applyFacts st (extractCond st false cond)
        let (stThen, failedThen) := stepList stTrueIn thenB sites
        let (stElse, failedElse) := stepList stFalseIn elseB sites
        let failed := failedThen ++ failedElse
        -- Pattern 1: 256-bit `checkedAdd`: `if (a + b < a) panic(0x11) else dest := a + b`.
        if let (.lt (.add a b) a', [.assignVar dest (.add a'' b'')]) := (cond, elseB) then
          if stThen.unreachable && exprStructEq a a' && exprStructEq a a'' &&
              exprStructEq b b'' then
            if let (some affA, some affB) := (affExact? st a, affExact? st b) then
              let (st1, gKey) := ghostHavoc dest st
              let key := VarKey.prog dest
              let sum := (affA.add affB).renameKey key gKey
              let st2 := applyFact { st1 with defs := st1.defs.insert key sum }
                (.leq sum (.ofConst maxWordVal))
              return (st2, failed)
        -- Pattern 2: narrow `checkedAdd`: `if (maxVal < a + b) panic(0x11) else dest := a + b`.
        if let (.lt (.literal maxVal) (.add a b), [.assignVar dest (.add a' b')]) :=
            (cond, elseB) then
          if stThen.unreachable && maxVal < 2 ^ 255 && exprStructEq a a' && exprStructEq b b' &&
              evalUpper st a + evalUpper st b < 2 ^ 256 then
            if let (some affA, some affB) := (affExact? st a, affExact? st b) then
              let (st1, gKey) := ghostHavoc dest st
              let key := VarKey.prog dest
              let sum := (affA.add affB).renameKey key gKey
              let st2 := applyFact
                { st1 with defs := st1.defs.insert key sum,
                           upper := st1.upper.insert key maxVal }
                (.leq sum (.ofConst maxVal))
              return (st2, failed)
        -- Pattern 3: `checkedSub`: `if (a < b) panic(0x11) else dest := a - b`.
        if let (.lt a b, [.assignVar dest (.sub a' b')]) := (cond, elseB) then
          if stThen.unreachable && exprStructEq a a' && exprStructEq b b' then
            let uA := evalUpper st a
            if let (some affA, some affB) := (affExact? st a, affExact? st b) then
              let (st1, gKey) := ghostHavoc dest st
              let key := VarKey.prog dest
              let affA' := affA.renameKey key gKey
              let affB' := affB.renameKey key gKey
              let stBase :=
                if uA < maxWordVal then { st1 with upper := st1.upper.insert key uA } else st1
              let stOut := match affA'.sub? affB' with
                | some diff => { stBase with defs := stBase.defs.insert key diff }
                | none =>
                    applyFacts stBase
                      [ .eq ((AffineNat.ofVar key).add affB') affA'
                      , .leq affB' affA' ]
              return (stOut, failed)
        -- Pattern 4: `checkedMul` by a constant factor.
        if let (.eq a (.literal 0), [.ite (.eq (.div (.mul a1 b1) a2) b2) okB panicB]) :=
            (cond, elseB) then
          if (stepList st panicB #[]).1.unreachable && exprStructEq a a1 && exprStructEq a a2 &&
              exprStructEq b1 b2 then
            if let (some (dest, prod), some (destThen, prodThen)) :=
                (checkedMulDest? okB, checkedMulDest? thenB) then
              if destThen == dest && exprStructEq prodThen prod &&
                  exprStructEq prod (.mul a b1) then
                let factor? : Option AffineNat := match affExact? st a, affExact? st b1 with
                  | some aAff, some bAff =>
                      if aAff.terms.isEmpty then some (bAff.scale aAff.const)
                      else if bAff.terms.isEmpty then some (aAff.scale bAff.const)
                      else none
                  | _, _ => none
                if let some prodAff := factor? then
                  let (st1, gKey) := ghostHavoc dest st
                  let key := VarKey.prog dest
                  let pAff := prodAff.renameKey key gKey
                  return (applyFact { st1 with defs := st1.defs.insert key pAff }
                    (.leq pAff (.ofConst maxWordVal)), failed)
        -- Pattern 5: `AbiEncoding.reserve` non-wraparound guard `if (finish >= base) {} else panic`.
        if let .ge (.localVar endName) (.localVar baseName) := cond then
          if stElse.unreachable && thenB.isEmpty &&
              evalUpper st (.localVar endName) ≤ maxAllocVal then
            if let some (recBase, szExpr) := st.reserveEnds.find? endName then
              if recBase == baseName then
                if let some sVar := reserveBoundedSizeVar? szExpr then
                  if evalUpper st (.localVar sVar) < 2 ^ 255 then
                    let curU := lookupKeyUpper stThen (.prog sVar)
                    return ({ stThen with
                      upper := stThen.upper.insert (.prog sVar) (min curU maxAllocVal) }, failed)
        -- General branch join: if one arm always halts/reverts, the surviving arm's facts hold.
        if stThen.unreachable && stElse.unreachable then
          ({ st with unreachable := true }, failed)
        else if stThen.unreachable then
          (stElse, failed)
        else if stElse.unreachable then
          (stThen, failed)
        else
          let assigned := (thenB.flatMap stmtAssignedNames ++
            elseB.flatMap stmtAssignedNames).eraseDups
          let stJoined := havocMany assigned st
          let joinedUpper := assigned.foldl
            (fun acc v =>
              let u := max (evalUpper stThen (.localVar v)) (evalUpper stElse (.localVar v))
              if u < maxWordVal then acc.insert (.prog v) u else acc)
            stJoined.upper
          ({ stJoined with upper := joinedUpper }, failed)
    | _ => (st, #[])

  /-- Match the exact two-statement short-circuit `&&` / `||` pair emitted by `Import.lean`:
  `.letVar dest lhsExpr :: .ite cond thenB elseB`, where `lhsExpr` and `cond` are structurally
  identical (`dest` is initialized to `cond` immediately before the branch). -/
  private partial def stepShortCircuit? (st : AbsState) (dest : String) (lhsExpr cond : Expr)
      (thenB elseB : List Stmt) (sites : Array McopySite) :
      Option (AbsState × Array McopySite) := Id.run do
    if st.unreachable || !exprStructEq lhsExpr cond then return none
    -- Short-circuit `&&`: `let dest := cond; if (cond) { pre; dest := rhsExpr } else {}`.
    if elseB.isEmpty && !thenB.isEmpty then
      if let some (.assignVar dest2 rhsExpr) := thenB.getLast? then
        let pre := thenB.dropLast
        let preLocals := (pre.flatMap stmtAssignedNames).eraseDups
        if dest2 == dest && !preLocals.contains dest &&
            (pre.flatMap stmtMutatedNames).isEmpty then
          let (st0, f0) := stepStmt st (.letVar dest lhsExpr) sites
          let stTrueIn := applyFacts st0 (extractCond st0 true cond)
          let (stThenPre, fPre) := stepList stTrueIn pre sites
          let (_, fLast) := stepStmt stThenPre (.assignVar dest rhsExpr) sites
          let allFailed := f0 ++ fPre ++ fLast
          if !st0.unreachable && !stThenPre.unreachable then
            let lhsTrue := extractCond st true cond
            let rhsTrue := (extractCond stThenPre true rhsExpr).filter fun f =>
              !factMentionsProgAny preLocals f
            let uRhs := evalUpper stThenPre rhsExpr
            let (st1, gKey) := ghostHavoc dest (havocMany preLocals st)
            let key := VarKey.prog dest
            let combined := (lhsTrue ++ rhsTrue).map (·.renameKey key gKey)
            return some
              ( { st1 with
                    upper := if uRhs < maxWordVal then st1.upper.insert key uRhs else st1.upper
                    boolTrue := if combined.isEmpty then st1.boolTrue
                      else st1.boolTrue.insert key combined },
                allFailed )
    -- Short-circuit `||`: `let dest := cond; if (cond) {} else { pre; dest := rhsExpr }`.
    if thenB.isEmpty && !elseB.isEmpty then
      if let some (.assignVar dest2 rhsExpr) := elseB.getLast? then
        let pre := elseB.dropLast
        let preLocals := (pre.flatMap stmtAssignedNames).eraseDups
        if dest2 == dest && !preLocals.contains dest &&
            (pre.flatMap stmtMutatedNames).isEmpty then
          let (st0, f0) := stepStmt st (.letVar dest lhsExpr) sites
          let stFalseIn := applyFacts st0 (extractCond st0 false cond)
          let (stElsePre, fPre) := stepList stFalseIn pre sites
          let (_, fLast) := stepStmt stElsePre (.assignVar dest rhsExpr) sites
          let allFailed := f0 ++ fPre ++ fLast
          if !st0.unreachable && !stElsePre.unreachable then
            let lhsFalse := extractCond st false cond
            let rhsFalse := (extractCond stElsePre false rhsExpr).filter fun f =>
              !factMentionsProgAny preLocals f
            let uJoin := max (evalUpper st lhsExpr) (evalUpper stElsePre rhsExpr)
            let (st1, gKey) := ghostHavoc dest (havocMany preLocals st)
            let key := VarKey.prog dest
            let combined := (lhsFalse ++ rhsFalse).map (·.renameKey key gKey)
            return some
              ( { st1 with
                    upper := if uJoin < maxWordVal then st1.upper.insert key uJoin else st1.upper
                    boolFalse := if combined.isEmpty then st1.boolFalse
                      else st1.boolFalse.insert key combined },
                allFailed )
    return none

  private partial def stepList (st : AbsState) (stmts : List Stmt) (sites : Array McopySite) :
      AbsState × Array McopySite :=
    match stmts with
    | [] => (st, #[])
    | .letVar dest lhsExpr :: .ite cond thenB elseB :: rest =>
        if let some (stNext, fPair) :=
            stepShortCircuit? st dest lhsExpr cond thenB elseB sites then
          let (stEnd, fRest) := stepList stNext rest sites
          (stEnd, fPair ++ fRest)
        else
          let (st1, f1) := stepStmt st (.letVar dest lhsExpr) sites
          let (st2, f2) := stepStmt st1 (.ite cond thenB elseB) sites
          let (stEnd, fRest) := stepList st2 rest sites
          (stEnd, f1 ++ f2 ++ fRest)
    | s :: rest =>
        let (st1, f1) := stepStmt st s sites
        let (stEnd, fRest) := stepList st1 rest sites
        (stEnd, f1 ++ fRest)
end

/-- Return all `mcopy` sites in `sites` that either touch a `ShortStrings` 32-byte inline-assembly
allocation (`shortStringPtrVars`) or whose positive-length source or destination range is not
proved in-bounds of its modelled buffer over `stmts`. -/
def unprovedMcopySites (stmts : List Stmt) (sites : Array McopySite)
    (shortStringPtrVars : Array String := #[]) : Array (McopySite × McopyFailureKind) :=
  if sites.isEmpty then #[] else
  let taintedPtrs := computePtrTaint stmts shortStringPtrVars
  let (taintedSites, cleanSites) := sites.partition fun site =>
    taintedPtrs.contains site.dstPtrVar || taintedPtrs.contains site.srcPtrVar
  let unprovedClean :=
    if cleanSites.isEmpty then #[] else (stepList {} stmts cleanSites).2
  taintedSites.map (·, .shortStringBuffer) ++ unprovedClean.map (·, .unprovedBounds)

/-- Return all `create2` sites whose underlying `initcodeTemplates` allocation pointer may flow
into the destination pointer (`dstPtrVar`) of any buffer `mcopy` site in `stmts` (across direct
writes, pointer aliases, ternaries, helper parameters, rebindings, or loop back-edges). -/
def clobberedCreate2Sites (stmts : List Stmt) (create2Sites : Array Create2TemplateSite)
    (mcopySites : Array McopySite) : Array Create2TemplateSite :=
  if create2Sites.isEmpty || mcopySites.isEmpty then #[] else
  create2Sites.filter fun c2 =>
    let tainted := computePtrTaint stmts #[c2.rootPtrVar]
    mcopySites.any fun m => tainted.contains m.dstPtrVar

end Compiler.CompilationModel.SolidityImport
