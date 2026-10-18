/-
  Source-expression closure under `BridgedExpr`.

  This module proves that the Verity compiler's `compileExpr` emits a
  `BridgedExpr` for the pure arithmetic / comparison / bit-operation
  fragment of the EDSL:
    - scalar/local leaves: `literal`, `param`, `constructorArg`, `localVar`,
      `arrayLength`
    - pure binops whose Yul output is `yulBinOp NAME (← a) (← b)` with
      `NAME ∈ bridgedBuiltins`: `add`, `sub`, `mul`, `div`, `sdiv`,
      `mod`, `smod`, `bitAnd`, `bitOr`, `bitXor`, `shl`, `shr`, `sar`,
      `signextend`, `eq`, `gt`, `sgt`, `lt`, `slt`
    - negated comparisons via `yulNegatedBinOp`: `ge`, `le`
    - boolean-normalized operations: `logicalAnd`, `logicalOr`, `logicalNot`
    - branchless arithmetic helpers: `ceilDiv`, `mulDivDown`, `mulDivUp`,
      `wMulDown`, `wDivUp`, `min`, `max`, `ite`
    - reserved exponentiation builtin surface:
      `externalCall builtinExpName [base, exponent]`
    - zero-argument environment/calldata-size reads whose emitted Yul calls
      are already bridged: `caller`, `contractAddress`, `msgValue`,
      `blockTimestamp`, `blockNumber`, `chainid`, `blobbasefee`,
      `calldatasize`
    - storage reads whose compiler field lookup succeeds: `storage`,
      `storageAddr`, `storageArrayLength`, `adtTag`, `adtField`
    - singleton and nested mapping reads through the abstract `mappingSlot`
      bridge: `mapping`, `mappingWord`, `mappingPackedWord`, `mappingUint`,
      `mapping2`, `mapping2Word`
    - single-mapping struct-member reads through the same `mappingSlot`
      bridge: `structMember`, `structMember2`
    - unary calldata/memory/transient reads: `calldataload`, `mload`, `tload`
    - native syntactic memory-slice hashing: `keccak256`

  General external/internal calls, checked
  dynamic-array elements, storage-array elements, ADT
  construction/matching, returndata, dynamic helpers, ABI casts,
  `selfBalance`, and external account/state reads are out of scope and require
  dedicated closure proofs.

  The scalar-leaf-only theorem `compileExpr_bridgedSource_leaf` is
  retained below as a specialization.

  Downstream `compileStmt` body-closure proofs compose this closure with
  per-constructor expression-subterm lifts.

  Run: lake build Compiler.Proofs.YulGeneration.Backends.EvmYulLeanSourceExprClosure
-/

import Compiler.Proofs.YulGeneration.Backends.EvmYulLeanBridgePredicates
import Compiler.Proofs.IRGeneration.ExprCore
import Compiler.CompilationModel.ExpressionCompile

namespace Compiler.Proofs.YulGeneration.Backends

open Compiler
open Compiler.Yul
open Compiler.CompilationModel
open Compiler.Proofs.IRGeneration
open Compiler.Proofs.YulGeneration

/-- Scalar leaf expressions of the EDSL whose `compileExpr` output is a
    `BridgedExpr`. Covers `literal`, `param`, `constructorArg`, `localVar`. -/
inductive BridgedSourceExprLeaf : Expr → Prop
  | literal (n : Nat) : BridgedSourceExprLeaf (.literal n)
  | param (name : String) : BridgedSourceExprLeaf (.param name)
  | constructorArg (idx : Nat) : BridgedSourceExprLeaf (.constructorArg idx)
  | localVar (name : String) : BridgedSourceExprLeaf (.localVar name)

/-- Scalar-leaf closure: every `BridgedSourceExprLeaf` compiles to a
    `BridgedExpr`. -/
theorem compileExpr_bridgedSource_leaf
    (fields : List CompilationModel.Field) (src : DynamicDataSource) :
    ∀ {e : Expr}, BridgedSourceExprLeaf e →
      ∀ {out : YulExpr}, compileExpr fields src e = .ok out → BridgedExpr out := by
  intro e hE out hOk
  cases hE with
  | literal n =>
      simp [compileExpr, compileExprWithInternals, Pure.pure, Except.pure] at hOk
      subst out
      exact BridgedExpr.lit _
  | param name =>
      simp [compileExpr, compileExprWithInternals, Pure.pure, Except.pure] at hOk
      subst out
      exact BridgedExpr.ident name
  | constructorArg idx =>
      simp [compileExpr, compileExprWithInternals, Pure.pure, Except.pure] at hOk
      subst out
      exact BridgedExpr.ident _
  | localVar name =>
      simp [compileExpr, compileExprWithInternals, Pure.pure, Except.pure] at hOk
      subst out
      exact BridgedExpr.ident name

/-- Source EDSL expressions whose `compileExpr` output is a `BridgedExpr`.
    Covers scalar/local leaves, storage reads whose compiler field lookup
    succeeds, including dynamic-array length words and ADT tag/field reads,
    singleton and nested mapping reads through the abstract `mappingSlot`
    bridge,
    mapping struct-member reads,
    pure arithmetic/comparison/bit-op binops, boolean-normalization forms,
    branchless arithmetic helpers, the reserved exponentiation builtin surface,
    zero-argument environment/calldata-size reads, unary calldata/memory/
    transient reads, syntactic memory-slice `keccak256`, and `ge`/`le` negated
    comparisons. General external/internal calls,
    checked dynamic-array elements, storage-array elements, ADT
    construction/matching, returndata, dynamic helpers, ABI casts,
    `selfBalance`, and external account/state reads are out of scope. -/
inductive BridgedSourceExpr : Expr → Prop
  -- scalar leaves
  | literal (n : Nat) : BridgedSourceExpr (.literal n)
  | param (name : String) : BridgedSourceExpr (.param name)
  | constructorArg (idx : Nat) : BridgedSourceExpr (.constructorArg idx)
  | localVar (name : String) : BridgedSourceExpr (.localVar name)
  | arrayLength (name : String) : BridgedSourceExpr (.arrayLength name)
  -- storage reads
  | storage (fieldName : String) : BridgedSourceExpr (.storage fieldName)
  | storageAddr (fieldName : String) : BridgedSourceExpr (.storageAddr fieldName)
  | storageArrayLength (fieldName : String) :
      BridgedSourceExpr (.storageArrayLength fieldName)
  | adtTag (adtName storageField : String) :
      BridgedSourceExpr (.adtTag adtName storageField)
  | adtField (adtName variantName fieldName : String) (fieldIndex : Nat)
      (storageField : String) :
      BridgedSourceExpr
        (.adtField adtName variantName fieldName fieldIndex storageField)
  | mapping {key : Expr} (fieldName : String) (hKey : BridgedSourceExpr key) :
      BridgedSourceExpr (.mapping fieldName key)
  | mappingWord {key : Expr} (fieldName : String) (hKey : BridgedSourceExpr key)
      (wordOffset : Nat) :
      BridgedSourceExpr (.mappingWord fieldName key wordOffset)
  | mappingPackedWord {key : Expr} (fieldName : String)
      (hKey : BridgedSourceExpr key) (wordOffset : Nat) (packed : PackedBits) :
      BridgedSourceExpr (.mappingPackedWord fieldName key wordOffset packed)
  | mappingUint {key : Expr} (fieldName : String) (hKey : BridgedSourceExpr key) :
      BridgedSourceExpr (.mappingUint fieldName key)
  | mapping2 {key1 key2 : Expr} (fieldName : String)
      (hKey1 : BridgedSourceExpr key1) (hKey2 : BridgedSourceExpr key2) :
      BridgedSourceExpr (.mapping2 fieldName key1 key2)
  | mapping2Word {key1 key2 : Expr} (fieldName : String)
      (hKey1 : BridgedSourceExpr key1) (hKey2 : BridgedSourceExpr key2)
      (wordOffset : Nat) :
      BridgedSourceExpr (.mapping2Word fieldName key1 key2 wordOffset)
  | structMember {key : Expr} (fieldName : String) (hKey : BridgedSourceExpr key)
      (memberName : String) :
      BridgedSourceExpr (.structMember fieldName key memberName)
  | structMember2 {key1 key2 : Expr} (fieldName : String)
      (hKey1 : BridgedSourceExpr key1) (hKey2 : BridgedSourceExpr key2)
      (memberName : String) :
      BridgedSourceExpr (.structMember2 fieldName key1 key2 memberName)
  -- zero-argument environment / calldata-size reads
  | caller : BridgedSourceExpr .caller
  | txOrigin : BridgedSourceExpr .txOrigin
  | contractAddress : BridgedSourceExpr .contractAddress
  | msgValue : BridgedSourceExpr .msgValue
  | blockTimestamp : BridgedSourceExpr .blockTimestamp
  | blockNumber : BridgedSourceExpr .blockNumber
  | chainid : BridgedSourceExpr .chainid
  | blobbasefee : BridgedSourceExpr .blobbasefee
  | calldatasize : BridgedSourceExpr .calldatasize
  | returndataSize : BridgedSourceExpr .returndataSize
  -- unary calldata / memory / transient reads
  | calldataload {offset} (hOffset : BridgedSourceExpr offset) :
      BridgedSourceExpr (.calldataload offset)
  | mload {offset} (hOffset : BridgedSourceExpr offset) :
      BridgedSourceExpr (.mload offset)
  | tload {offset} (hOffset : BridgedSourceExpr offset) :
      BridgedSourceExpr (.tload offset)
  | extcodesize {addr} (hAddr : BridgedSourceExpr addr) :
      BridgedSourceExpr (.extcodesize addr)
  | returndataOptionalBoolAt {offset} (hOffset : BridgedSourceExpr offset) :
      BridgedSourceExpr (.returndataOptionalBoolAt offset)
  | keccak256 {offset size}
      (hOffset : BridgedSourceExpr offset) (hSize : BridgedSourceExpr size) :
      BridgedSourceExpr (.keccak256 offset size)
  -- arithmetic binops (yulBinOp with bridged name)
  | add {a b} (ha : BridgedSourceExpr a) (hb : BridgedSourceExpr b) :
      BridgedSourceExpr (.add a b)
  | sub {a b} (ha : BridgedSourceExpr a) (hb : BridgedSourceExpr b) :
      BridgedSourceExpr (.sub a b)
  | mul {a b} (ha : BridgedSourceExpr a) (hb : BridgedSourceExpr b) :
      BridgedSourceExpr (.mul a b)
  | div {a b} (ha : BridgedSourceExpr a) (hb : BridgedSourceExpr b) :
      BridgedSourceExpr (.div a b)
  | sdiv {a b} (ha : BridgedSourceExpr a) (hb : BridgedSourceExpr b) :
      BridgedSourceExpr (.sdiv a b)
  | mod {a b} (ha : BridgedSourceExpr a) (hb : BridgedSourceExpr b) :
      BridgedSourceExpr (.mod a b)
  | smod {a b} (ha : BridgedSourceExpr a) (hb : BridgedSourceExpr b) :
      BridgedSourceExpr (.smod a b)
  -- bit operation binops
  | bitAnd {a b} (ha : BridgedSourceExpr a) (hb : BridgedSourceExpr b) :
      BridgedSourceExpr (.bitAnd a b)
  | bitOr {a b} (ha : BridgedSourceExpr a) (hb : BridgedSourceExpr b) :
      BridgedSourceExpr (.bitOr a b)
  | bitXor {a b} (ha : BridgedSourceExpr a) (hb : BridgedSourceExpr b) :
      BridgedSourceExpr (.bitXor a b)
  | bitNot {a} (ha : BridgedSourceExpr a) :
      BridgedSourceExpr (.bitNot a)
  -- shift binops
  | shl {s v} (hs : BridgedSourceExpr s) (hv : BridgedSourceExpr v) :
      BridgedSourceExpr (.shl s v)
  | shr {s v} (hs : BridgedSourceExpr s) (hv : BridgedSourceExpr v) :
      BridgedSourceExpr (.shr s v)
  | sar {s v} (hs : BridgedSourceExpr s) (hv : BridgedSourceExpr v) :
      BridgedSourceExpr (.sar s v)
  | byte {i v} (hi : BridgedSourceExpr i) (hv : BridgedSourceExpr v) :
      BridgedSourceExpr (.byte i v)
  | signextend {b v} (hb : BridgedSourceExpr b) (hv : BridgedSourceExpr v) :
      BridgedSourceExpr (.signextend b v)
  -- direct comparison binops
  | eq {a b} (ha : BridgedSourceExpr a) (hb : BridgedSourceExpr b) :
      BridgedSourceExpr (.eq a b)
  | gt {a b} (ha : BridgedSourceExpr a) (hb : BridgedSourceExpr b) :
      BridgedSourceExpr (.gt a b)
  | sgt {a b} (ha : BridgedSourceExpr a) (hb : BridgedSourceExpr b) :
      BridgedSourceExpr (.sgt a b)
  | lt {a b} (ha : BridgedSourceExpr a) (hb : BridgedSourceExpr b) :
      BridgedSourceExpr (.lt a b)
  | slt {a b} (ha : BridgedSourceExpr a) (hb : BridgedSourceExpr b) :
      BridgedSourceExpr (.slt a b)
  -- boolean normalization
  | logicalAnd {a b} (ha : BridgedSourceExpr a) (hb : BridgedSourceExpr b) :
      BridgedSourceExpr (.logicalAnd a b)
  | logicalOr {a b} (ha : BridgedSourceExpr a) (hb : BridgedSourceExpr b) :
      BridgedSourceExpr (.logicalOr a b)
  | logicalNot {a} (ha : BridgedSourceExpr a) :
      BridgedSourceExpr (.logicalNot a)
  -- branchless arithmetic helpers
  | ceilDiv {a b} (ha : BridgedSourceExpr a) (hb : BridgedSourceExpr b) :
      BridgedSourceExpr (.ceilDiv a b)
  | mulDivDown {a b c}
      (ha : BridgedSourceExpr a) (hb : BridgedSourceExpr b)
      (hc : BridgedSourceExpr c) :
      BridgedSourceExpr (.mulDivDown a b c)
  | mulDivUp {a b c}
      (ha : BridgedSourceExpr a) (hb : BridgedSourceExpr b)
      (hc : BridgedSourceExpr c) :
      BridgedSourceExpr (.mulDivUp a b c)
  | wMulDown {a b} (ha : BridgedSourceExpr a) (hb : BridgedSourceExpr b) :
      BridgedSourceExpr (.wMulDown a b)
  | wDivUp {a b} (ha : BridgedSourceExpr a) (hb : BridgedSourceExpr b) :
      BridgedSourceExpr (.wDivUp a b)
  | builtinExp {base exponent}
      (hBase : BridgedSourceExpr base) (hExponent : BridgedSourceExpr exponent) :
      BridgedSourceExpr (.externalCall builtinExpName [base, exponent])
  | min {a b} (ha : BridgedSourceExpr a) (hb : BridgedSourceExpr b) :
      BridgedSourceExpr (.min a b)
  | max {a b} (ha : BridgedSourceExpr a) (hb : BridgedSourceExpr b) :
      BridgedSourceExpr (.max a b)
  | ite {cond thenVal elseVal}
      (hCond : BridgedSourceExpr cond) (hThen : BridgedSourceExpr thenVal)
      (hElse : BridgedSourceExpr elseVal) :
      BridgedSourceExpr (.ite cond thenVal elseVal)
  -- negated comparisons (yulNegatedBinOp)
  | ge {a b} (ha : BridgedSourceExpr a) (hb : BridgedSourceExpr b) :
      BridgedSourceExpr (.ge a b)
  | le {a b} (ha : BridgedSourceExpr a) (hb : BridgedSourceExpr b) :
      BridgedSourceExpr (.le a b)

/-- The public IR compile-core expression grammar is contained in the native
    source-expression bridge. This turns `SupportedFragment` expression
    witnesses into the `BridgedSourceExpr` premises consumed by body-closure
    proofs. -/
theorem bridgedSourceExpr_of_exprCompileCore :
    ∀ {e : Expr}, FunctionBody.ExprCompileCore e → BridgedSourceExpr e := by
  intro e hCore
  induction hCore <;> constructor <;> assumption

/-- A syntactic memory-slice `keccak256` expression is native-bridged when its
    offset and size arguments are in the public compile-core expression
    grammar. This does not add `keccak256` to `ExprCompileCore`: source/IR
    semantic correctness still needs source-side memory-slice hashing. -/
theorem bridgedSourceExpr_keccak256_of_exprCompileCore
    {offset size : Expr}
    (hOffset : FunctionBody.ExprCompileCore offset)
    (hSize : FunctionBody.ExprCompileCore size) :
    BridgedSourceExpr (.keccak256 offset size) :=
  BridgedSourceExpr.keccak256
    (bridgedSourceExpr_of_exprCompileCore hOffset)
    (bridgedSourceExpr_of_exprCompileCore hSize)

/-- A `YulExpr.call` whose name is in `bridgedBuiltins` and whose two
    arguments are already `BridgedExpr` is itself a `BridgedExpr`. -/
private theorem bridgedExpr_binopBuiltin {func : String}
    (hBridged : func ∈ bridgedBuiltins) {a b : YulExpr}
    (ha : BridgedExpr a) (hb : BridgedExpr b) :
    BridgedExpr (YulExpr.call func [a, b]) := by
  refine BridgedExpr.call func [a, b] (Or.inl hBridged) ?_
  intro arg hMem
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hMem
  rcases hMem with rfl | rfl
  · exact ha
  · exact hb

/-- A `YulExpr.call` whose name is in `bridgedBuiltins` and whose single
    argument is already a `BridgedExpr` is itself a `BridgedExpr`. -/
private theorem bridgedExpr_unopBuiltin {func : String}
    (hBridged : func ∈ bridgedBuiltins) {a : YulExpr}
    (ha : BridgedExpr a) :
    BridgedExpr (YulExpr.call func [a]) := by
  refine BridgedExpr.call func [a] (Or.inl hBridged) ?_
  intro arg hMem
  simp only [List.mem_singleton] at hMem
  subst hMem
  exact ha

/-- A zero-argument `YulExpr.call` whose name is in `bridgedBuiltins` is a
    `BridgedExpr`. -/
private theorem bridgedExpr_nullaryBuiltin {func : String}
    (hBridged : func ∈ bridgedBuiltins) :
    BridgedExpr (YulExpr.call func []) := by
  refine BridgedExpr.call func [] (Or.inl hBridged) ?_
  intro arg hMem
  cases hMem

/-- `yulBinOp op a b` is bridged when `op ∈ bridgedBuiltins` and both
    arguments are bridged. -/
private theorem bridgedExpr_yulBinOp {func : String}
    (hBridged : func ∈ bridgedBuiltins) {a b : YulExpr}
    (ha : BridgedExpr a) (hb : BridgedExpr b) :
    BridgedExpr (yulBinOp func a b) := by
  unfold yulBinOp
  exact bridgedExpr_binopBuiltin hBridged ha hb

/-- `yulNegatedBinOp op a b = iszero(call op [a, b])` is bridged when
    `op ∈ bridgedBuiltins` and both arguments are bridged. -/
private theorem bridgedExpr_yulNegatedBinOp {func : String}
    (hBridged : func ∈ bridgedBuiltins) {a b : YulExpr}
    (ha : BridgedExpr a) (hb : BridgedExpr b) :
    BridgedExpr (yulNegatedBinOp func a b) := by
  unfold yulNegatedBinOp
  exact bridgedExpr_unopBuiltin (by simp [bridgedBuiltins])
    (bridgedExpr_binopBuiltin hBridged ha hb)

/-- `yulToBool e = iszero(iszero(e))` is bridged when `e` is bridged. -/
private theorem bridgedExpr_yulToBool {e : YulExpr} (hE : BridgedExpr e) :
    BridgedExpr (yulToBool e) := by
  unfold yulToBool
  exact bridgedExpr_unopBuiltin (by simp [bridgedBuiltins])
    (bridgedExpr_unopBuiltin (by simp [bridgedBuiltins]) hE)

private theorem bridgedExpr_ceilDiv {a b : YulExpr}
    (ha : BridgedExpr a) (hb : BridgedExpr b) :
    BridgedExpr
      (YulExpr.call "mul" [
        YulExpr.call "iszero" [YulExpr.call "iszero" [a]],
        YulExpr.call "add" [
          YulExpr.call "div" [YulExpr.call "sub" [a, YulExpr.lit 1], b],
          YulExpr.lit 1
        ]
      ]) := by
  have hBool : BridgedExpr (YulExpr.call "iszero" [YulExpr.call "iszero" [a]]) :=
    bridgedExpr_yulToBool ha
  have hSub : BridgedExpr (YulExpr.call "sub" [a, YulExpr.lit 1]) :=
    bridgedExpr_binopBuiltin (by simp [bridgedBuiltins]) ha (BridgedExpr.lit 1)
  have hDiv : BridgedExpr (YulExpr.call "div" [YulExpr.call "sub" [a, YulExpr.lit 1], b]) :=
    bridgedExpr_binopBuiltin (by simp [bridgedBuiltins]) hSub hb
  have hAdd :
      BridgedExpr
        (YulExpr.call "add" [
          YulExpr.call "div" [YulExpr.call "sub" [a, YulExpr.lit 1], b],
          YulExpr.lit 1]) :=
    bridgedExpr_binopBuiltin (by simp [bridgedBuiltins]) hDiv (BridgedExpr.lit 1)
  exact bridgedExpr_binopBuiltin (by simp [bridgedBuiltins]) hBool hAdd

private theorem bridgedExpr_mulDivDown {a b c : YulExpr}
    (ha : BridgedExpr a) (hb : BridgedExpr b) (hc : BridgedExpr c) :
    BridgedExpr (YulExpr.call "div" [YulExpr.call "mul" [a, b], c]) := by
  exact bridgedExpr_binopBuiltin (by simp [bridgedBuiltins])
    (bridgedExpr_binopBuiltin (by simp [bridgedBuiltins]) ha hb) hc

private theorem bridgedExpr_mulDivUp {a b c : YulExpr}
    (ha : BridgedExpr a) (hb : BridgedExpr b) (hc : BridgedExpr c) :
    BridgedExpr
      (YulExpr.call "div" [
        YulExpr.call "add" [
          YulExpr.call "mul" [a, b],
          YulExpr.call "sub" [c, YulExpr.lit 1]
        ],
        c
      ]) := by
  have hMul : BridgedExpr (YulExpr.call "mul" [a, b]) :=
    bridgedExpr_binopBuiltin (by simp [bridgedBuiltins]) ha hb
  have hSub : BridgedExpr (YulExpr.call "sub" [c, YulExpr.lit 1]) :=
    bridgedExpr_binopBuiltin (by simp [bridgedBuiltins]) hc (BridgedExpr.lit 1)
  have hAdd :
      BridgedExpr
        (YulExpr.call "add" [
          YulExpr.call "mul" [a, b],
          YulExpr.call "sub" [c, YulExpr.lit 1]]) :=
    bridgedExpr_binopBuiltin (by simp [bridgedBuiltins]) hMul hSub
  exact bridgedExpr_binopBuiltin (by simp [bridgedBuiltins]) hAdd hc

private theorem bridgedExpr_wMulDown {a b : YulExpr}
    (ha : BridgedExpr a) (hb : BridgedExpr b) :
    BridgedExpr
      (YulExpr.call "div" [
        YulExpr.call "mul" [a, b],
        YulExpr.lit 1000000000000000000]) := by
  exact bridgedExpr_binopBuiltin (by simp [bridgedBuiltins])
    (bridgedExpr_binopBuiltin (by simp [bridgedBuiltins]) ha hb)
    (BridgedExpr.lit 1000000000000000000)

private theorem bridgedExpr_wDivUp {a b : YulExpr}
    (ha : BridgedExpr a) (hb : BridgedExpr b) :
    BridgedExpr
      (YulExpr.call "div" [
        YulExpr.call "add" [
          YulExpr.call "mul" [a, YulExpr.lit 1000000000000000000],
          YulExpr.call "sub" [b, YulExpr.lit 1]
        ],
        b
      ]) := by
  have hMul :
      BridgedExpr
        (YulExpr.call "mul" [a, YulExpr.lit 1000000000000000000]) :=
    bridgedExpr_binopBuiltin (by simp [bridgedBuiltins]) ha
      (BridgedExpr.lit 1000000000000000000)
  have hSub : BridgedExpr (YulExpr.call "sub" [b, YulExpr.lit 1]) :=
    bridgedExpr_binopBuiltin (by simp [bridgedBuiltins]) hb (BridgedExpr.lit 1)
  have hAdd :
      BridgedExpr
        (YulExpr.call "add" [
          YulExpr.call "mul" [a, YulExpr.lit 1000000000000000000],
          YulExpr.call "sub" [b, YulExpr.lit 1]]) :=
    bridgedExpr_binopBuiltin (by simp [bridgedBuiltins]) hMul hSub
  exact bridgedExpr_binopBuiltin (by simp [bridgedBuiltins]) hAdd hb

private theorem bridgedExpr_min {a b : YulExpr}
    (ha : BridgedExpr a) (hb : BridgedExpr b) :
    BridgedExpr
      (YulExpr.call "sub" [a,
        YulExpr.call "mul" [
          YulExpr.call "sub" [a, b],
          YulExpr.call "gt" [a, b]
        ]
      ]) := by
  have hSub : BridgedExpr (YulExpr.call "sub" [a, b]) :=
    bridgedExpr_binopBuiltin (by simp [bridgedBuiltins]) ha hb
  have hGt : BridgedExpr (YulExpr.call "gt" [a, b]) :=
    bridgedExpr_binopBuiltin (by simp [bridgedBuiltins]) ha hb
  have hMul :
      BridgedExpr
        (YulExpr.call "mul" [YulExpr.call "sub" [a, b], YulExpr.call "gt" [a, b]]) :=
    bridgedExpr_binopBuiltin (by simp [bridgedBuiltins]) hSub hGt
  exact bridgedExpr_binopBuiltin (by simp [bridgedBuiltins]) ha hMul

private theorem bridgedExpr_max {a b : YulExpr}
    (ha : BridgedExpr a) (hb : BridgedExpr b) :
    BridgedExpr
      (YulExpr.call "add" [a,
        YulExpr.call "mul" [
          YulExpr.call "sub" [b, a],
          YulExpr.call "gt" [b, a]
        ]
      ]) := by
  have hSub : BridgedExpr (YulExpr.call "sub" [b, a]) :=
    bridgedExpr_binopBuiltin (by simp [bridgedBuiltins]) hb ha
  have hGt : BridgedExpr (YulExpr.call "gt" [b, a]) :=
    bridgedExpr_binopBuiltin (by simp [bridgedBuiltins]) hb ha
  have hMul :
      BridgedExpr
        (YulExpr.call "mul" [YulExpr.call "sub" [b, a], YulExpr.call "gt" [b, a]]) :=
    bridgedExpr_binopBuiltin (by simp [bridgedBuiltins]) hSub hGt
  exact bridgedExpr_binopBuiltin (by simp [bridgedBuiltins]) ha hMul

private theorem bridgedExpr_ite {cond thenVal elseVal : YulExpr}
    (hCond : BridgedExpr cond) (hThen : BridgedExpr thenVal)
    (hElse : BridgedExpr elseVal) :
    BridgedExpr
      (YulExpr.call "add" [
        YulExpr.call "mul" [
          YulExpr.call "iszero" [YulExpr.call "iszero" [cond]], thenVal],
        YulExpr.call "mul" [YulExpr.call "iszero" [cond], elseVal]
      ]) := by
  have hBool : BridgedExpr (YulExpr.call "iszero" [YulExpr.call "iszero" [cond]]) :=
    bridgedExpr_yulToBool hCond
  have hNeg : BridgedExpr (YulExpr.call "iszero" [cond]) :=
    bridgedExpr_unopBuiltin (by simp [bridgedBuiltins]) hCond
  have hThenTerm :
      BridgedExpr
        (YulExpr.call "mul" [
          YulExpr.call "iszero" [YulExpr.call "iszero" [cond]], thenVal]) :=
    bridgedExpr_binopBuiltin (by simp [bridgedBuiltins]) hBool hThen
  have hElseTerm :
      BridgedExpr (YulExpr.call "mul" [YulExpr.call "iszero" [cond], elseVal]) :=
    bridgedExpr_binopBuiltin (by simp [bridgedBuiltins]) hNeg hElse
  exact bridgedExpr_binopBuiltin (by simp [bridgedBuiltins]) hThenTerm hElseTerm

/-- Literal-slot `sload` is in the native bridged expression fragment. -/
private theorem bridgedExpr_sload_lit (slot : Nat) :
    BridgedExpr (YulExpr.call "sload" [YulExpr.lit slot]) := by
  refine BridgedExpr.call "sload" _ (Or.inl (by simp [bridgedBuiltins])) ?_
  intro arg hMem
  simp only [List.mem_singleton] at hMem
  subst arg
  exact BridgedExpr.lit slot

/-- `sload(e)` is in the native bridged expression fragment whenever the slot
    expression is bridged. -/
private theorem bridgedExpr_sload {slot : YulExpr} (hSlot : BridgedExpr slot) :
    BridgedExpr (YulExpr.call "sload" [slot]) := by
  refine BridgedExpr.call "sload" _ (Or.inl (by simp [bridgedBuiltins])) ?_
  intro arg hMem
  simp only [List.mem_singleton] at hMem
  subst arg
  exact hSlot

private theorem bridgedExpr_storageLoad (isTransient : Bool)
    {slot : YulExpr} (hSlot : BridgedExpr slot) :
    BridgedExpr
      (YulExpr.call (if isTransient then "tload" else "sload") [slot]) := by
  cases isTransient
  · exact bridgedExpr_sload hSlot
  · exact bridgedExpr_tload slot hSlot

private theorem bridgedExpr_storageLoad_lit (isTransient : Bool) (slot : Nat) :
    BridgedExpr
      (YulExpr.call (if isTransient then "tload" else "sload")
        [YulExpr.lit slot]) :=
  bridgedExpr_storageLoad isTransient (BridgedExpr.lit slot)

/-- `mappingSlot(base, key)` is in the native bridged expression fragment
    whenever both slot arguments are bridged. -/
private theorem bridgedExpr_mappingSlot {base key : YulExpr}
    (hBase : BridgedExpr base) (hKey : BridgedExpr key) :
    BridgedExpr (YulExpr.call "mappingSlot" [base, key]) :=
  bridgedExpr_binopBuiltin (by simp [bridgedBuiltins]) hBase hKey

/-- `sload(mappingSlot(lit slot, key))` is bridged for bridged keys. -/
private theorem bridgedExpr_sload_mappingSlot_lit
    (slot : Nat) {key : YulExpr} (hKey : BridgedExpr key) :
    BridgedExpr
      (YulExpr.call "sload"
        [YulExpr.call "mappingSlot" [YulExpr.lit slot, key]]) :=
  bridgedExpr_sload
    (bridgedExpr_mappingSlot (BridgedExpr.lit slot) hKey)

private theorem bridgedExpr_storageLoad_mappingSlot_lit
    (isTransient : Bool) (slot : Nat) {key : YulExpr}
    (hKey : BridgedExpr key) :
    BridgedExpr
      (YulExpr.call (if isTransient then "tload" else "sload")
        [YulExpr.call "mappingSlot" [YulExpr.lit slot, key]]) :=
  bridgedExpr_storageLoad isTransient
    (bridgedExpr_mappingSlot (BridgedExpr.lit slot) hKey)

/-- `sload(add(mappingSlot(lit slot, key), lit wordOffset))` is bridged for
    bridged keys. -/
private theorem bridgedExpr_sload_mappingSlot_lit_add
    (slot wordOffset : Nat) {key : YulExpr} (hKey : BridgedExpr key) :
    BridgedExpr
      (YulExpr.call "sload"
        [YulExpr.call "add"
          [YulExpr.call "mappingSlot" [YulExpr.lit slot, key],
            YulExpr.lit wordOffset]]) :=
  bridgedExpr_sload
    (bridgedExpr_binopBuiltin (by simp [bridgedBuiltins])
      (bridgedExpr_mappingSlot (BridgedExpr.lit slot) hKey)
      (BridgedExpr.lit wordOffset))

private theorem bridgedExpr_storageLoad_mappingSlot_lit_add
    (isTransient : Bool) (slot wordOffset : Nat) {key : YulExpr}
    (hKey : BridgedExpr key) :
    BridgedExpr
      (YulExpr.call (if isTransient then "tload" else "sload")
        [YulExpr.call "add"
          [YulExpr.call "mappingSlot" [YulExpr.lit slot, key],
            YulExpr.lit wordOffset]]) :=
  bridgedExpr_storageLoad isTransient
    (bridgedExpr_binopBuiltin (by simp [bridgedBuiltins])
      (bridgedExpr_mappingSlot (BridgedExpr.lit slot) hKey)
      (BridgedExpr.lit wordOffset))

private theorem bridgedExpr_storageLoad_mappingSlot_lit_offset
    (isTransient : Bool) (slot wordOffset : Nat) {key : YulExpr}
    (hKey : BridgedExpr key) :
    BridgedExpr
      (YulExpr.call (if isTransient then "tload" else "sload")
        [if wordOffset = 0 then
          YulExpr.call "mappingSlot" [YulExpr.lit slot, key]
        else
          YulExpr.call "add"
            [YulExpr.call "mappingSlot" [YulExpr.lit slot, key],
              YulExpr.lit wordOffset]]) := by
  by_cases hOffset : wordOffset = 0
  · simp [hOffset]
    exact bridgedExpr_storageLoad_mappingSlot_lit isTransient slot hKey
  · simp [hOffset]
    exact bridgedExpr_storageLoad_mappingSlot_lit_add
      isTransient slot wordOffset hKey

/-- `sload(mappingSlot(mappingSlot(lit slot, key1), key2))` is bridged for
    bridged nested mapping keys. -/
private theorem bridgedExpr_sload_mappingSlot2_lit
    (slot : Nat) {key1 key2 : YulExpr}
    (hKey1 : BridgedExpr key1) (hKey2 : BridgedExpr key2) :
    BridgedExpr
      (YulExpr.call "sload"
        [YulExpr.call "mappingSlot"
          [YulExpr.call "mappingSlot" [YulExpr.lit slot, key1], key2]]) :=
  bridgedExpr_sload
    (bridgedExpr_mappingSlot
      (bridgedExpr_mappingSlot (BridgedExpr.lit slot) hKey1)
      hKey2)

private theorem bridgedExpr_storageLoad_mappingSlot2_lit
    (isTransient : Bool) (slot : Nat) {key1 key2 : YulExpr}
    (hKey1 : BridgedExpr key1) (hKey2 : BridgedExpr key2) :
    BridgedExpr
      (YulExpr.call (if isTransient then "tload" else "sload")
        [YulExpr.call "mappingSlot"
          [YulExpr.call "mappingSlot" [YulExpr.lit slot, key1], key2]]) :=
  bridgedExpr_storageLoad isTransient
    (bridgedExpr_mappingSlot
      (bridgedExpr_mappingSlot (BridgedExpr.lit slot) hKey1)
      hKey2)

/-- `sload(add(mappingSlot(mappingSlot(lit slot, key1), key2), lit
    wordOffset))` is bridged for bridged nested mapping keys. -/
private theorem bridgedExpr_sload_mappingSlot2_lit_add
    (slot wordOffset : Nat) {key1 key2 : YulExpr}
    (hKey1 : BridgedExpr key1) (hKey2 : BridgedExpr key2) :
    BridgedExpr
      (YulExpr.call "sload"
        [YulExpr.call "add"
          [YulExpr.call "mappingSlot"
            [YulExpr.call "mappingSlot" [YulExpr.lit slot, key1], key2],
            YulExpr.lit wordOffset]]) :=
  bridgedExpr_sload
    (bridgedExpr_binopBuiltin (by simp [bridgedBuiltins])
      (bridgedExpr_mappingSlot
        (bridgedExpr_mappingSlot (BridgedExpr.lit slot) hKey1)
        hKey2)
      (BridgedExpr.lit wordOffset))

private theorem bridgedExpr_storageLoad_mappingSlot2_lit_add
    (isTransient : Bool) (slot wordOffset : Nat) {key1 key2 : YulExpr}
    (hKey1 : BridgedExpr key1) (hKey2 : BridgedExpr key2) :
    BridgedExpr
      (YulExpr.call (if isTransient then "tload" else "sload")
        [YulExpr.call "add"
          [YulExpr.call "mappingSlot"
            [YulExpr.call "mappingSlot" [YulExpr.lit slot, key1], key2],
            YulExpr.lit wordOffset]]) :=
  bridgedExpr_storageLoad isTransient
    (bridgedExpr_binopBuiltin (by simp [bridgedBuiltins])
      (bridgedExpr_mappingSlot
        (bridgedExpr_mappingSlot (BridgedExpr.lit slot) hKey1)
        hKey2)
      (BridgedExpr.lit wordOffset))

private theorem bridgedExpr_storageLoad_mappingSlot2_lit_offset
    (isTransient : Bool) (slot wordOffset : Nat) {key1 key2 : YulExpr}
    (hKey1 : BridgedExpr key1) (hKey2 : BridgedExpr key2) :
    BridgedExpr
      (YulExpr.call (if isTransient then "tload" else "sload")
        [if wordOffset = 0 then
          YulExpr.call "mappingSlot"
            [YulExpr.call "mappingSlot" [YulExpr.lit slot, key1], key2]
        else
          YulExpr.call "add"
            [YulExpr.call "mappingSlot"
              [YulExpr.call "mappingSlot" [YulExpr.lit slot, key1], key2],
              YulExpr.lit wordOffset]]) := by
  by_cases hOffset : wordOffset = 0
  · simp [hOffset]
    exact bridgedExpr_storageLoad_mappingSlot2_lit
      isTransient slot hKey1 hKey2
  · simp [hOffset]
    exact bridgedExpr_storageLoad_mappingSlot2_lit_add
      isTransient slot wordOffset hKey1 hKey2

private theorem bridgedExpr_resolvedStorageLoad_mappingSlot2_lit
    (fields : List CompilationModel.Field) (fieldName : String)
    (slot : Nat) {key1 key2 : YulExpr}
    (hKey1 : BridgedExpr key1) (hKey2 : BridgedExpr key2) :
    BridgedExpr
      (YulExpr.call
        (match findFieldWithResolvedSlot fields fieldName with
        | some (f, _) => if f.isTransient then "tload" else "sload"
        | none => "sload")
        [YulExpr.call "mappingSlot"
          [YulExpr.call "mappingSlot" [YulExpr.lit slot, key1], key2]]) := by
  cases hResolved : findFieldWithResolvedSlot fields fieldName with
  | none =>
      simpa [hResolved] using
        bridgedExpr_storageLoad_mappingSlot2_lit false slot hKey1 hKey2
  | some resolved =>
      cases resolved with
      | mk f resolvedSlot =>
          simpa [hResolved] using
            bridgedExpr_storageLoad_mappingSlot2_lit f.isTransient slot hKey1 hKey2

private theorem bridgedExpr_resolvedStorageLoad_mappingSlot2_lit_offset
    (fields : List CompilationModel.Field) (fieldName : String)
    (slot wordOffset : Nat) {key1 key2 : YulExpr}
    (hKey1 : BridgedExpr key1) (hKey2 : BridgedExpr key2) :
    BridgedExpr
      (YulExpr.call
        (match findFieldWithResolvedSlot fields fieldName with
        | some (f, _) => if f.isTransient then "tload" else "sload"
        | none => "sload")
        [if wordOffset = 0 then
          YulExpr.call "mappingSlot"
            [YulExpr.call "mappingSlot" [YulExpr.lit slot, key1], key2]
        else
          YulExpr.call "add"
            [YulExpr.call "mappingSlot"
              [YulExpr.call "mappingSlot" [YulExpr.lit slot, key1], key2],
              YulExpr.lit wordOffset]]) := by
  cases hResolved : findFieldWithResolvedSlot fields fieldName with
  | none =>
      simpa [hResolved] using
        bridgedExpr_storageLoad_mappingSlot2_lit_offset
          false slot wordOffset hKey1 hKey2
  | some resolved =>
      cases resolved with
      | mk f resolvedSlot =>
          simpa [hResolved] using
            bridgedExpr_storageLoad_mappingSlot2_lit_offset
              f.isTransient slot wordOffset hKey1 hKey2

/-- A `foldl mappingSlot` chain over bridged key expressions stays in the
    native bridged expression fragment. -/
private theorem bridgedExpr_foldl_mappingSlot
    (keys : List YulExpr) {base : YulExpr}
    (hBase : BridgedExpr base)
    (hKeys : ∀ key ∈ keys, BridgedExpr key) :
    BridgedExpr
      (keys.foldl
        (fun slotExpr keyExpr =>
          YulExpr.call "mappingSlot" [slotExpr, keyExpr])
        base) := by
  induction keys generalizing base with
  | nil =>
      simpa using hBase
  | cons key rest ih =>
      simp only [List.foldl_cons]
      have hKey : BridgedExpr key := hKeys key (by simp)
      have hRest : ∀ k ∈ rest, BridgedExpr k := by
        intro k hk
        exact hKeys k (by simp [hk])
      exact ih (bridgedExpr_mappingSlot hBase hKey) hRest

/-- `sload(compileMappingSlotChain(lit slot, keys))` is bridged when every
    compiled key is bridged. -/
private theorem bridgedExpr_sload_mappingSlotChain_lit
    (slot : Nat) (keys : List YulExpr)
    (hKeys : ∀ key ∈ keys, BridgedExpr key) :
    BridgedExpr
      (YulExpr.call "sload"
        [compileMappingSlotChain (YulExpr.lit slot) keys]) := by
  unfold compileMappingSlotChain
  exact bridgedExpr_sload
    (bridgedExpr_foldl_mappingSlot keys (BridgedExpr.lit slot) hKeys)

private theorem bridgedExpr_storageLoad_mappingSlotChain_lit
    (isTransient : Bool) (slot : Nat) (keys : List YulExpr)
    (hKeys : ∀ key ∈ keys, BridgedExpr key) :
    BridgedExpr
      (YulExpr.call (if isTransient then "tload" else "sload")
        [compileMappingSlotChain (YulExpr.lit slot) keys]) := by
  unfold compileMappingSlotChain
  exact bridgedExpr_storageLoad isTransient
    (bridgedExpr_foldl_mappingSlot keys (BridgedExpr.lit slot) hKeys)

private theorem bridgedExpr_resolvedStorageLoad_mappingSlotChain_lit
    (fields : List CompilationModel.Field) (fieldName : String)
    (slot : Nat) (keys : List YulExpr)
    (hKeys : ∀ key ∈ keys, BridgedExpr key) :
    BridgedExpr
      (YulExpr.call
        (match findFieldWithResolvedSlot fields fieldName with
        | some (f, _) => if f.isTransient then "tload" else "sload"
        | none => "sload")
        [compileMappingSlotChain (YulExpr.lit slot) keys]) := by
  cases hResolved : findFieldWithResolvedSlot fields fieldName with
  | none =>
      simpa [hResolved] using
        bridgedExpr_storageLoad_mappingSlotChain_lit false slot keys hKeys
  | some resolved =>
      cases resolved with
      | mk f resolvedSlot =>
          simpa [hResolved] using
            bridgedExpr_storageLoad_mappingSlotChain_lit
              f.isTransient slot keys hKeys

/-- The compiler's singleton mapping-read helper emits only native-bridged
    Yul when field lookup succeeds and the key expression is bridged.

    The proof intentionally stays at the `mappingSlot` helper boundary; it does
    not claim source-level memory+keccak equivalence for mapping slots. -/
private theorem compileMappingSlotRead_bridged
    {fields : List CompilationModel.Field} {field label : String}
    {keyExpr out : YulExpr} {wordOffset : Nat}
    (hKey : BridgedExpr keyExpr)
    (hOk :
      compileMappingSlotRead fields field keyExpr label wordOffset = .ok out) :
    BridgedExpr out := by
  unfold compileMappingSlotRead at hOk
  split at hOk
  · simp at hOk
  · split at hOk
    · rename_i f slot hFind
      dsimp at hOk
      simp [Pure.pure, Except.pure] at hOk
      subst out
      exact bridgedExpr_storageLoad_mappingSlot_lit_offset
        f.isTransient slot wordOffset hKey
    · simp at hOk

/-- ADT tag reads compile to `and(sload(baseSlot), 0xff)`. -/
private theorem bridgedExpr_adtTagRead_lit (baseSlot : Nat) :
    BridgedExpr (compileAdtTagRead (YulExpr.lit baseSlot)) := by
  unfold compileAdtTagRead
  exact bridgedExpr_binopBuiltin (by simp [bridgedBuiltins])
    (bridgedExpr_sload_lit baseSlot) (BridgedExpr.lit 0xFF)

/-- ADT field reads compile to `sload(add(baseSlot, fieldIndex + 1))`. -/
private theorem bridgedExpr_adtFieldRead_lit (baseSlot fieldIndex : Nat) :
    BridgedExpr (compileAdtFieldRead (YulExpr.lit baseSlot) fieldIndex) := by
  unfold compileAdtFieldRead
  exact bridgedExpr_sload
    (bridgedExpr_binopBuiltin (by simp [bridgedBuiltins])
      (BridgedExpr.lit baseSlot) (BridgedExpr.lit (fieldIndex + 1)))

/-- Packed storage reads compile to `and(shr(offset, sload(slot)), mask)`,
    whose subexpressions are all native bridged builtins. -/
private theorem bridgedExpr_packed_sload_lit
    (slot offset mask : Nat) :
    BridgedExpr
      (YulExpr.call "and"
        [YulExpr.call "shr" [YulExpr.lit offset,
            YulExpr.call "sload" [YulExpr.lit slot]],
          YulExpr.lit mask]) := by
  refine BridgedExpr.call "and" _ (Or.inl (by simp [bridgedBuiltins])) ?_
  intro arg hMem
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hMem
  rcases hMem with rfl | rfl
  · refine BridgedExpr.call "shr" _ (Or.inl (by simp [bridgedBuiltins])) ?_
    intro arg hMem
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hMem
    rcases hMem with rfl | rfl
    · exact BridgedExpr.lit offset
    · exact bridgedExpr_sload_lit slot
  · exact BridgedExpr.lit mask

/-- Packed reads over an already-bridged slot word compile to
    `and(shr(offset, slotWord), mask)`, whose subexpressions are bridged. -/
private theorem bridgedExpr_packed_read
    {slotWord : YulExpr} (hSlotWord : BridgedExpr slotWord)
    (offset mask : Nat) :
    BridgedExpr
      (YulExpr.call "and"
        [YulExpr.call "shr" [YulExpr.lit offset, slotWord],
          YulExpr.lit mask]) := by
  refine BridgedExpr.call "and" _ (Or.inl (by simp [bridgedBuiltins])) ?_
  intro arg hMem
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hMem
  rcases hMem with rfl | rfl
  · refine BridgedExpr.call "shr" _ (Or.inl (by simp [bridgedBuiltins])) ?_
    intro arg hMem
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hMem
    rcases hMem with rfl | rfl
    · exact BridgedExpr.lit offset
    · exact hSlotWord
  · exact BridgedExpr.lit mask

/-- Destructure a binary helper expression emission. -/
private theorem compileExpr_binaryShape_ok
    {fields : List CompilationModel.Field} {src : DynamicDataSource}
    {shape : YulExpr → YulExpr → YulExpr} {a b : Expr} {out : YulExpr}
    (hOk : (do let x ← compileExpr fields src a
               let y ← compileExpr fields src b
               pure (shape x y) : Except String YulExpr) = .ok out) :
    ∃ ca cb, compileExpr fields src a = .ok ca
           ∧ compileExpr fields src b = .ok cb
           ∧ out = shape ca cb := by
  cases hA : compileExpr fields src a with
  | error e => simp [hA, bind, Except.bind] at hOk
  | ok ca =>
      cases hB : compileExpr fields src b with
      | error e => simp [hA, hB, bind, Except.bind] at hOk
      | ok cb =>
          refine ⟨ca, cb, rfl, rfl, ?_⟩
          simp [hA, hB, bind, Except.bind, Pure.pure, Except.pure] at hOk
          exact hOk.symm

/-- Destructure a ternary helper expression emission. -/
private theorem compileExpr_ternaryShape_ok
    {fields : List CompilationModel.Field} {src : DynamicDataSource}
    {shape : YulExpr → YulExpr → YulExpr → YulExpr}
    {a b c : Expr} {out : YulExpr}
    (hOk : (do let x ← compileExpr fields src a
               let y ← compileExpr fields src b
               let z ← compileExpr fields src c
               pure (shape x y z) : Except String YulExpr) = .ok out) :
    ∃ ca cb cc, compileExpr fields src a = .ok ca
              ∧ compileExpr fields src b = .ok cb
              ∧ compileExpr fields src c = .ok cc
              ∧ out = shape ca cb cc := by
  cases hA : compileExpr fields src a with
  | error e => simp [hA, bind, Except.bind] at hOk
  | ok ca =>
      cases hB : compileExpr fields src b with
      | error e => simp [hA, hB, bind, Except.bind] at hOk
      | ok cb =>
          cases hC : compileExpr fields src c with
          | error e => simp [hA, hB, hC, bind, Except.bind] at hOk
          | ok cc =>
              refine ⟨ca, cb, cc, rfl, rfl, rfl, ?_⟩
              simp [hA, hB, hC, bind, Except.bind, Pure.pure, Except.pure] at hOk
              exact hOk.symm

/-- A unary emission `shape (← compileExpr a)` is bridged when `shape` preserves
    bridging and the subterm compiles to bridged Yul. -/
private theorem bridged_of_unaryShape_ok
    {fields : List CompilationModel.Field} {src : DynamicDataSource}
    {shape : YulExpr → YulExpr} {a : Expr} {out : YulExpr}
    (hShape : ∀ {x}, BridgedExpr x → BridgedExpr (shape x))
    (iha : ∀ {o : YulExpr}, compileExpr fields src a = .ok o → BridgedExpr o)
    (hOk : (do let x ← compileExpr fields src a
               pure (shape x) : Except String YulExpr) = .ok out) :
    BridgedExpr out := by
  cases hA : compileExpr fields src a with
  | error e => simp [hA, bind, Except.bind] at hOk
  | ok ca =>
      simp [hA, bind, Except.bind, Pure.pure, Except.pure] at hOk
      subst hOk
      exact hShape (iha hA)

/-- A binary emission `shape (← compileExpr a) (← compileExpr b)` is bridged when
    `shape` preserves bridging and both subterms compile to bridged Yul. -/
private theorem bridged_of_binaryShape_ok
    {fields : List CompilationModel.Field} {src : DynamicDataSource}
    {shape : YulExpr → YulExpr → YulExpr} {a b : Expr} {out : YulExpr}
    (hShape : ∀ {x y}, BridgedExpr x → BridgedExpr y → BridgedExpr (shape x y))
    (iha : ∀ {o : YulExpr}, compileExpr fields src a = .ok o → BridgedExpr o)
    (ihb : ∀ {o : YulExpr}, compileExpr fields src b = .ok o → BridgedExpr o)
    (hOk : (do let x ← compileExpr fields src a
               let y ← compileExpr fields src b
               pure (shape x y) : Except String YulExpr) = .ok out) :
    BridgedExpr out := by
  obtain ⟨ca, cb, hA, hB, rfl⟩ := compileExpr_binaryShape_ok hOk
  exact hShape (iha hA) (ihb hB)

/-- A ternary emission `shape (← a) (← b) (← c)` is bridged when `shape`
    preserves bridging and all three subterms compile to bridged Yul. -/
private theorem bridged_of_ternaryShape_ok
    {fields : List CompilationModel.Field} {src : DynamicDataSource}
    {shape : YulExpr → YulExpr → YulExpr → YulExpr} {a b c : Expr} {out : YulExpr}
    (hShape : ∀ {x y z}, BridgedExpr x → BridgedExpr y → BridgedExpr z →
      BridgedExpr (shape x y z))
    (iha : ∀ {o : YulExpr}, compileExpr fields src a = .ok o → BridgedExpr o)
    (ihb : ∀ {o : YulExpr}, compileExpr fields src b = .ok o → BridgedExpr o)
    (ihc : ∀ {o : YulExpr}, compileExpr fields src c = .ok o → BridgedExpr o)
    (hOk : (do let x ← compileExpr fields src a
               let y ← compileExpr fields src b
               let z ← compileExpr fields src c
               pure (shape x y z) : Except String YulExpr) = .ok out) :
    BridgedExpr out := by
  obtain ⟨ca, cb, cc, hA, hB, hC, rfl⟩ := compileExpr_ternaryShape_ok hOk
  exact hShape (iha hA) (ihb hB) (ihc hC)

/-- Boolean-normalized binops `op(yulToBool a, yulToBool b)` are bridged. -/
private theorem bridgedExpr_yulBoolBinOp {func : String}
    (hBridged : func ∈ bridgedBuiltins) {a b : YulExpr}
    (ha : BridgedExpr a) (hb : BridgedExpr b) :
    BridgedExpr (yulBinOp func (yulToBool a) (yulToBool b)) :=
  bridgedExpr_yulBinOp hBridged (bridgedExpr_yulToBool ha) (bridgedExpr_yulToBool hb)

/-- Plain storage reads compile to bridged (possibly packed) literal-slot loads. -/
private theorem compileExpr_storage_bridged
    {fields : List CompilationModel.Field} {src : DynamicDataSource}
    {fieldName : String} {out : YulExpr}
    (hOk : compileExpr fields src (.storage fieldName) = .ok out) :
    BridgedExpr out := by
  simp only [compileExpr, compileExprWithInternals] at hOk
  split at hOk
  · simp at hOk
  · split at hOk
    · rename_i f slot hFind
      cases hPacked : f.packedBits with
      | none =>
          simp [hPacked, Pure.pure, Except.pure] at hOk
          subst out
          exact bridgedExpr_storageLoad_lit f.isTransient slot
      | some packed =>
          simp [hPacked, Pure.pure, Except.pure] at hOk
          subst out
          exact bridgedExpr_packed_read
            (bridgedExpr_storageLoad_lit f.isTransient slot) packed.offset
            (packedMaskNat packed)
    · simp at hOk

/-- Address-typed storage reads compile to bridged (possibly packed) loads. -/
private theorem compileExpr_storageAddr_bridged
    {fields : List CompilationModel.Field} {src : DynamicDataSource}
    {fieldName : String} {out : YulExpr}
    (hOk : compileExpr fields src (.storageAddr fieldName) = .ok out) :
    BridgedExpr out := by
  simp only [compileExpr, compileExprWithInternals] at hOk
  split at hOk
  · simp at hOk
  · split at hOk
    · rename_i f slot hFind
      cases hTy : f.ty <;> simp [hTy] at hOk
      cases hPacked : f.packedBits with
      | none =>
          simp [hPacked, Pure.pure, Except.pure] at hOk
          subst out
          exact bridgedExpr_storageLoad_lit f.isTransient slot
      | some packed =>
          simp [hPacked, Pure.pure, Except.pure] at hOk
          subst out
          exact bridgedExpr_packed_read
            (bridgedExpr_storageLoad_lit f.isTransient slot) packed.offset
            (packedMaskNat packed)
    · simp at hOk

/-- Dynamic-array length reads compile to a bridged literal-slot `sload`. -/
private theorem compileExpr_storageArrayLength_bridged
    {fields : List CompilationModel.Field} {src : DynamicDataSource}
    {fieldName : String} {out : YulExpr}
    (hOk : compileExpr fields src (.storageArrayLength fieldName) = .ok out) :
    BridgedExpr out := by
  simp only [compileExpr, compileExprWithInternals] at hOk
  split at hOk
  · rename_i f slot hFind
    cases hTy : f.ty <;> simp [hTy, Pure.pure, Except.pure] at hOk
    subst out
    exact bridgedExpr_sload_lit slot
  · simp at hOk

/-- ADT tag reads compile to bridged Yul when the storage field resolves. -/
private theorem compileExpr_adtTag_bridged
    {fields : List CompilationModel.Field} {src : DynamicDataSource}
    {adtName storageField : String} {out : YulExpr}
    (hOk : compileExpr fields src (.adtTag adtName storageField) = .ok out) :
    BridgedExpr out := by
  simp only [compileExpr, compileExprWithInternals] at hOk
  split at hOk
  · rename_i baseSlot hFind
    simp [Pure.pure, Except.pure] at hOk
    subst out
    exact bridgedExpr_adtTagRead_lit baseSlot
  · simp at hOk

/-- ADT field reads compile to bridged Yul when the storage field resolves. -/
private theorem compileExpr_adtField_bridged
    {fields : List CompilationModel.Field} {src : DynamicDataSource}
    {adtName variantName fieldName storageField : String} {fieldIndex : Nat}
    {out : YulExpr}
    (hOk : compileExpr fields src
      (.adtField adtName variantName fieldName fieldIndex storageField) = .ok out) :
    BridgedExpr out := by
  simp only [compileExpr, compileExprWithInternals] at hOk
  split at hOk
  · rename_i baseSlot hFind
    simp [Pure.pure, Except.pure] at hOk
    subst out
    exact bridgedExpr_adtFieldRead_lit baseSlot fieldIndex
  · simp at hOk

/-- A mapping read `compileMappingSlotRead … (← compileExpr key) …` is bridged
    whenever the key compiles to bridged Yul. -/
private theorem bridged_of_mappingSlotRead_ok
    {fields : List CompilationModel.Field} {src : DynamicDataSource}
    {fieldName label : String} {key : Expr} {wordOffset : Nat} {out : YulExpr}
    (ih : ∀ {o : YulExpr}, compileExpr fields src key = .ok o → BridgedExpr o)
    (hOk : (do
        compileMappingSlotRead fields fieldName (← compileExpr fields src key)
          label wordOffset : Except String YulExpr) = .ok out) :
    BridgedExpr out := by
  cases hK : compileExpr fields src key with
  | error err => simp [hK, bind, Except.bind] at hOk
  | ok k =>
      simp only [hK, bind, Except.bind] at hOk
      exact compileMappingSlotRead_bridged (ih hK) hOk

/-- A packed read `and(shr(offset, slotWord), mask)` over a mapping slot word is
    bridged whenever the key compiles to bridged Yul. -/
private theorem bridged_of_packedMappingSlotRead_ok
    {fields : List CompilationModel.Field} {src : DynamicDataSource}
    {fieldName label : String} {key : Expr} {wordOffset : Nat} {packed : PackedBits}
    {out : YulExpr}
    (ih : ∀ {o : YulExpr}, compileExpr fields src key = .ok o → BridgedExpr o)
    (hOk : (do
        let slotWord ← compileMappingSlotRead fields fieldName
          (← compileExpr fields src key) label wordOffset
        pure (YulExpr.call "and" [YulExpr.call "shr" [YulExpr.lit packed.offset, slotWord],
          YulExpr.lit (packedMaskNat packed)]) : Except String YulExpr) = .ok out) :
    BridgedExpr out := by
  cases hK : compileExpr fields src key with
  | error err => simp [hK, bind, Except.bind] at hOk
  | ok k =>
      cases hSlot : compileMappingSlotRead fields fieldName k label wordOffset with
      | error err => simp [hK, hSlot, bind, Except.bind] at hOk
      | ok slotWord =>
          simp [hK, hSlot, bind, Except.bind, Pure.pure, Except.pure] at hOk
          subst out
          exact bridgedExpr_packed_read (compileMappingSlotRead_bridged (ih hK) hSlot) _ _

/-- Packed single-mapping word reads compile to bridged Yul. -/
private theorem compileExpr_mappingPackedWord_bridged
    {fields : List CompilationModel.Field} {src : DynamicDataSource}
    {fieldName : String} {key : Expr} {wordOffset : Nat} {packed : PackedBits}
    {out : YulExpr}
    (ih : ∀ {o : YulExpr}, compileExpr fields src key = .ok o → BridgedExpr o)
    (hOk : compileExpr fields src (.mappingPackedWord fieldName key wordOffset packed)
      = .ok out) :
    BridgedExpr out := by
  simp only [compileExpr, compileExprWithInternals] at hOk
  split at hOk
  · simp at hOk
  · exact bridged_of_packedMappingSlotRead_ok ih hOk

/-- Double-mapping reads compile to a bridged load over nested `mappingSlot`s. -/
private theorem compileExpr_mapping2_bridged
    {fields : List CompilationModel.Field} {src : DynamicDataSource}
    {fieldName : String} {key1 key2 : Expr} {out : YulExpr}
    (ih1 : ∀ {o : YulExpr}, compileExpr fields src key1 = .ok o → BridgedExpr o)
    (ih2 : ∀ {o : YulExpr}, compileExpr fields src key2 = .ok o → BridgedExpr o)
    (hOk : compileExpr fields src (.mapping2 fieldName key1 key2) = .ok out) :
    BridgedExpr out := by
  simp only [compileExpr, compileExprWithInternals] at hOk
  split at hOk
  · simp at hOk
  · split at hOk
    · rename_i f slot hFind
      obtain ⟨c1, c2, h1, h2, rfl⟩ := compileExpr_binaryShape_ok hOk
      simpa [hFind] using
        bridgedExpr_resolvedStorageLoad_mappingSlot2_lit fields fieldName slot (ih1 h1) (ih2 h2)
    · simp at hOk

/-- Double-mapping word reads compile to a bridged load over nested
    `mappingSlot`s plus an optional word offset. -/
private theorem compileExpr_mapping2Word_bridged
    {fields : List CompilationModel.Field} {src : DynamicDataSource}
    {fieldName : String} {key1 key2 : Expr} {wordOffset : Nat} {out : YulExpr}
    (ih1 : ∀ {o : YulExpr}, compileExpr fields src key1 = .ok o → BridgedExpr o)
    (ih2 : ∀ {o : YulExpr}, compileExpr fields src key2 = .ok o → BridgedExpr o)
    (hOk : compileExpr fields src (.mapping2Word fieldName key1 key2 wordOffset) = .ok out) :
    BridgedExpr out := by
  simp only [compileExpr, compileExprWithInternals] at hOk
  split at hOk
  · simp at hOk
  · split at hOk
    · rename_i f slot hFind
      obtain ⟨c1, c2, h1, h2, rfl⟩ := compileExpr_binaryShape_ok hOk
      simpa [hFind] using
        bridgedExpr_resolvedStorageLoad_mappingSlot2_lit_offset fields fieldName slot
          wordOffset (ih1 h1) (ih2 h2)
    · simp at hOk

/-- Single-mapping struct-member reads compile to bridged (possibly packed)
    mapping slot reads. -/
private theorem compileExpr_structMember_bridged
    {fields : List CompilationModel.Field} {src : DynamicDataSource}
    {fieldName memberName : String} {key : Expr} {out : YulExpr}
    (ih : ∀ {o : YulExpr}, compileExpr fields src key = .ok o → BridgedExpr o)
    (hOk : compileExpr fields src (.structMember fieldName key memberName) = .ok out) :
    BridgedExpr out := by
  simp only [compileExpr, compileExprWithInternals] at hOk
  split at hOk
  · cases hOk
  · simp only [pure_bind] at hOk
    split at hOk
    · simp at hOk
    · split at hOk
      · simp at hOk
      · rename_i member hMember
        cases hPacked : member.packed <;> simp only [hPacked] at hOk
        · exact bridged_of_mappingSlotRead_ok ih hOk
        · exact bridged_of_packedMappingSlotRead_ok ih hOk

/-- Double-mapping struct-member reads compile to bridged (possibly packed)
    loads over nested `mappingSlot`s. -/
private theorem compileExpr_structMember2_bridged
    {fields : List CompilationModel.Field} {src : DynamicDataSource}
    {fieldName memberName : String} {key1 key2 : Expr} {out : YulExpr}
    (ih1 : ∀ {o : YulExpr}, compileExpr fields src key1 = .ok o → BridgedExpr o)
    (ih2 : ∀ {o : YulExpr}, compileExpr fields src key2 = .ok o → BridgedExpr o)
    (hOk : compileExpr fields src (.structMember2 fieldName key1 key2 memberName)
      = .ok out) :
    BridgedExpr out := by
  simp only [compileExpr, compileExprWithInternals] at hOk
  split at hOk
  · simp at hOk
  · split at hOk
    · simp at hOk
    · split at hOk
      · simp at hOk
      · rename_i member hMember
        split at hOk
        · rename_i f slot hFind
          have hLoad := fun {c1 c2 : YulExpr} (h1 : BridgedExpr c1) (h2 : BridgedExpr c2) =>
            bridgedExpr_resolvedStorageLoad_mappingSlot2_lit_offset fields fieldName slot
              member.wordOffset h1 h2
          cases hPacked : member.packed <;> simp only [hPacked] at hOk <;>
            obtain ⟨c1, c2, h1, h2, rfl⟩ := compileExpr_binaryShape_ok hOk
          · simpa [hFind] using hLoad (ih1 h1) (ih2 h2)
          · simpa [hFind] using bridgedExpr_packed_read (hLoad (ih1 h1) (ih2 h2)) _ _
        · simp at hOk

/-- The reserved exponentiation builtin compiles to a bridged `exp` call. -/
private theorem compileExpr_builtinExp_bridged
    {fields : List CompilationModel.Field} {src : DynamicDataSource}
    {base exponent : Expr} {out : YulExpr}
    (iha : ∀ {o : YulExpr}, compileExpr fields src base = .ok o → BridgedExpr o)
    (ihb : ∀ {o : YulExpr}, compileExpr fields src exponent = .ok o → BridgedExpr o)
    (hOk : compileExpr fields src (.externalCall builtinExpName [base, exponent])
      = .ok out) :
    BridgedExpr out := by
  simp only [compileExpr, compileExprWithInternals] at hOk
  cases hA : compileExprWithInternals fields src [] base with
  | error err => simp [compileExprListWithInternals, hA, bind, Except.bind] at hOk
  | ok ca =>
      cases hB : compileExprWithInternals fields src [] exponent with
      | error err => simp [compileExprListWithInternals, hA, hB, bind, Except.bind] at hOk
      | ok cb =>
          simp [compileExprListWithInternals, hA, hB, builtinExpName, Pure.pure,
            Except.pure, bind, Except.bind] at hOk
          cases hOk
          exact bridgedExpr_yulBinOp (by simp [bridgedBuiltins]) (iha hA) (ihb hB)

/-- Main theorem: every `BridgedSourceExpr` compiles to a `BridgedExpr`.
    Structural induction on the source predicate. Leaf and storage cases are
    discharged directly or by per-constructor helpers; unary/binary/ternary
    operator cases destructure the emitted do-block with the generic
    `bridged_of_*Shape_ok` helpers and close the shape obligation with the
    matching `bridgedExpr_*` lemma. -/
theorem compileExpr_bridgedSource
    (fields : List CompilationModel.Field) (src : DynamicDataSource) :
    ∀ {e : Expr}, BridgedSourceExpr e →
      ∀ {out : YulExpr}, compileExpr fields src e = .ok out → BridgedExpr out := by
  intro e hE
  induction hE <;> intro out hOk
  case literal | param | constructorArg | localVar | arrayLength | caller | txOrigin
      | contractAddress | msgValue | blockTimestamp | blockNumber | chainid | blobbasefee
      | calldatasize | returndataSize =>
    simp [compileExpr, compileExprWithInternals, Pure.pure, Except.pure] at hOk
    subst out
    first
      | exact BridgedExpr.lit _ | exact BridgedExpr.ident _
      | exact bridgedExpr_nullaryBuiltin (by simp [bridgedBuiltins])
  case storage => exact compileExpr_storage_bridged hOk
  case storageAddr => exact compileExpr_storageAddr_bridged hOk
  case storageArrayLength => exact compileExpr_storageArrayLength_bridged hOk
  case adtTag => exact compileExpr_adtTag_bridged hOk
  case adtField => exact compileExpr_adtField_bridged hOk
  case mapping | mappingWord | mappingUint =>
    simp only [compileExpr, compileExprWithInternals] at hOk
    exact bridged_of_mappingSlotRead_ok ‹_› hOk
  case mappingPackedWord => exact compileExpr_mappingPackedWord_bridged ‹_› hOk
  case mapping2 => exact compileExpr_mapping2_bridged ‹_› ‹_› hOk
  case mapping2Word => exact compileExpr_mapping2Word_bridged ‹_› ‹_› hOk
  case structMember => exact compileExpr_structMember_bridged ‹_› hOk
  case structMember2 => exact compileExpr_structMember2_bridged ‹_› ‹_› hOk
  case builtinExp => exact compileExpr_builtinExp_bridged ‹_› ‹_› hOk
  all_goals
    simp only [compileExpr, compileExprWithInternals] at hOk
    first
      | refine bridged_of_unaryShape_ok ?_ ‹_› hOk
      | refine bridged_of_binaryShape_ok ?_ ‹_› ‹_› hOk
      | refine bridged_of_ternaryShape_ok ?_ ‹_› ‹_› ‹_› hOk
    first
      | exact bridgedExpr_mload _ | exact bridgedExpr_tload _ | exact bridgedExpr_extcodesize _
      | exact bridgedExpr_returndataOptionalBoolAt _ | exact bridgedExpr_keccak256 _ _
      | exact bridgedExpr_unopBuiltin (by simp [bridgedBuiltins])
      | exact bridgedExpr_yulBinOp (by simp [bridgedBuiltins])
      | exact bridgedExpr_yulNegatedBinOp (by simp [bridgedBuiltins])
      | exact bridgedExpr_yulBoolBinOp (by simp [bridgedBuiltins]) | exact bridgedExpr_ceilDiv
      | exact bridgedExpr_wMulDown | exact bridgedExpr_wDivUp
      | exact bridgedExpr_min | exact bridgedExpr_max | exact bridgedExpr_mulDivDown
      | exact bridgedExpr_mulDivUp | exact bridgedExpr_ite

/-- Convenience wrapper for the native syntactic `keccak256` source-expression
    closure when the offset and size subexpressions are compile-core. -/
theorem compileExpr_keccak256_bridgedSource_of_exprCompileCore
    (fields : List CompilationModel.Field) (src : DynamicDataSource)
    {offset size : Expr} {out : YulExpr}
    (hOffset : FunctionBody.ExprCompileCore offset)
    (hSize : FunctionBody.ExprCompileCore size)
    (hOk : compileExpr fields src (.keccak256 offset size) = .ok out) :
    BridgedExpr out :=
  compileExpr_bridgedSource fields src
    (bridgedSourceExpr_keccak256_of_exprCompileCore hOffset hSize)
    hOk

/-- Default `require` failure condition shape: `iszero(compileExpr cond)` is
    bridged whenever the source condition expression is bridged. -/
private theorem compileRequireFailCond_default_bridgedSource
    {fields : List CompilationModel.Field} {src : DynamicDataSource}
    {cond : Expr} {failCond : YulExpr}
    (hCond : BridgedSourceExpr cond)
    (hOk :
      (do
        let compiled ← compileExpr fields src cond
        pure (YulExpr.call "iszero" [compiled]) : Except String YulExpr) = .ok failCond) :
    BridgedExpr failCond := by
  cases hCompiled : compileExpr fields src cond with
  | error err =>
      rw [hCompiled] at hOk
      cases hOk
  | ok compiled =>
      rw [hCompiled] at hOk
      cases hOk
      exact bridgedExpr_unopBuiltin (by simp [bridgedBuiltins])
        (compileExpr_bridgedSource fields src hCond hCompiled)

/-- `compileRequireFailCond` emits a `BridgedExpr` for every pure bridged source
    condition. The `ge`/`le` cases use the compiler's direct negation
    optimization (`lt`/`gt`); all other conditions compile as `iszero(cond)`. -/
theorem compileRequireFailCond_bridgedSource
    (fields : List CompilationModel.Field) (src : DynamicDataSource) :
    ∀ {cond : Expr}, BridgedSourceExpr cond →
      ∀ {failCond : YulExpr},
        compileRequireFailCond fields src cond = .ok failCond → BridgedExpr failCond := by
  intro cond hCond failCond hOk
  cases cond
  case ge | le =>
    cases hCond
    simp only [compileRequireFailCond] at hOk
    exact bridged_of_binaryShape_ok (bridgedExpr_yulBinOp (by simp [bridgedBuiltins]))
      (compileExpr_bridgedSource fields src ‹_›) (compileExpr_bridgedSource fields src ‹_›) hOk
  all_goals exact compileRequireFailCond_default_bridgedSource hCond hOk

/-- List-level closure: when every source expression in a list is
    `BridgedSourceExpr`, `compileExprList` produces a list whose every
    element is a `BridgedExpr`.

    Used by body-closure lemmas for statement constructors that carry a
    list of source expressions (e.g., `rawLog`, `emit`, `setMapping`
    multi-slot, `setStructMember`, `returnValues`, `ecm` args). -/
theorem compileExprList_bridgedSource
    (fields : List CompilationModel.Field) (src : DynamicDataSource) :
    ∀ {exprs : List Expr}, (∀ e ∈ exprs, BridgedSourceExpr e) →
      ∀ {out : List YulExpr},
        compileExprList fields src exprs = .ok out →
        ∀ yulExpr ∈ out, BridgedExpr yulExpr := by
  intro exprs
  induction exprs with
  | nil =>
      intro _ out hOk
      simp [compileExprList, compileExprListWithInternals, Pure.pure, Except.pure] at hOk
      subst out
      intro yulExpr hMem
      cases hMem
  | cons e es ih =>
      intro hAll out hOk
      simp only [compileExprList, compileExprListWithInternals, bind, Except.bind] at hOk
      cases hHead : compileExprWithInternals fields src [] e with
      | error err =>
          simp [hHead] at hOk
      | ok headExpr =>
          simp [hHead] at hOk
          cases hTail : compileExprListWithInternals fields src [] es with
          | error err =>
              simp [hTail] at hOk
          | ok tailExprs =>
              simp [hTail, Pure.pure, Except.pure] at hOk
              subst out
              have hHeadSource : BridgedSourceExpr e := hAll e (by simp)
              have hHeadBridged : BridgedExpr headExpr :=
                compileExpr_bridgedSource fields src hHeadSource hHead
              have hTailAll : ∀ e' ∈ es, BridgedSourceExpr e' := by
                intro e' hMem
                exact hAll e' (by simp [hMem])
              have hTailBridged : ∀ x ∈ tailExprs, BridgedExpr x :=
                ih hTailAll hTail
              intro yulExpr hMem
              simp only [List.mem_cons] at hMem
              cases hMem with
              | inl h => subst h; exact hHeadBridged
              | inr h => exact hTailBridged yulExpr h

/-- Mapping-chain source-expression wrapper: when every key source expression
    is in `BridgedSourceExpr`, the compiler's `mappingChain` read emits a
    bridged `sload` over a `foldl mappingSlot` chain.

    Like the other mapping read closures, this stays at the abstract
    `mappingSlot` helper boundary rather than claiming source-level
    memory+keccak equivalence. -/
theorem compileExpr_mappingChain_bridgedSource
    (fields : List CompilationModel.Field) (src : DynamicDataSource)
    {fieldName : String} {keys : List Expr} {out : YulExpr}
    (hKeys : ∀ key ∈ keys, BridgedSourceExpr key)
    (hOk : compileExpr fields src (.mappingChain fieldName keys) = .ok out) :
    BridgedExpr out := by
  simp only [compileExpr, compileExprWithInternals] at hOk
  split at hOk
  · simp at hOk
  · split at hOk
    · rename_i f slot hFind
      cases hCompiledKeys : compileExprListWithInternals fields src [] keys with
      | error err =>
          simp [bind, Except.bind, hCompiledKeys] at hOk
      | ok keyExprs =>
          simp [bind, Except.bind, hCompiledKeys, Pure.pure, Except.pure] at hOk
          subst out
          exact bridgedExpr_storageLoad_mappingSlotChain_lit
            f.isTransient slot keyExprs
            (compileExprList_bridgedSource fields src hKeys hCompiledKeys)
    · simp at hOk

end Compiler.Proofs.YulGeneration.Backends
