/-
Copyright (c) 2026 Verity Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Verity Authors
-/
import Lean
import Verity.Macro.Syntax
import Verity.Macro.Types
import Verity.Macro.Storage
import Verity.Macro.Interfaces

namespace Verity.Macro

open Lean
open Lean.Elab.Command

set_option hygiene false

/-!
# Macro Inheritance Resolution (`#2419`, `#2420`)

This module provides reusable resolution and layout helpers for single- and
multi-parent contract inheritance in `verity_contract`:

1. **Inherited Storage Slot Offsetting (`#2420`)**:
   - `storageFieldSlotSpan`: computes the number of 256-bit storage slots occupied
     by a `StorageFieldDecl` (including ADTs and `FixedArray` strides).
   - `contractStorageSlotWatermark`: computes the next available slot index after
     all fields of an ancestor contract.
   - `offsetInheritedStorageField` / `offsetInheritedStorageAccessorTree` /
     `composeInheritedStorageLayout`: shifts inherited or child relative storage
     slots and detects overlapping slot/bitfield collisions.
2. **Child-Scope `override` Method Resolution (`#2419`)**:
   - `inheritanceSignatureKey`: canonical `(name, paramTypes)` dispatch key.
   - `validateMethodOverride`: checks `virtual`, mutability (`payable`/`view`/`pure`),
     visibility (`internal`), and return-type compatibility.
   - `resolveChildOverrideMethods`: resolves child `override` declarations against
     inherited parent functions while retaining shadowed parent implementations as
     internal helpers for `super.f(args)` dispatch.
3. **`super.f(args)` Call Resolution (`#2419`)**:
   - `superMethodMangledName`: canonical internal helper name `__super_<Parent>_<method>`.
   - `resolveSuperCallTarget?`: resolves `super.f(args)` along the C3 / right-to-left
     parent linearization.
   - `parseSuperCallSyntax?` / `rewriteSuperCallTerm`: rewrites `super.f(args)` into
     a direct internal call to the retained ancestor implementation.
-/

/-! ## 1. Inherited Storage Slot Offsetting (`#2420`) -/

/-- Number of 256-bit storage slots occupied by `field` (`#2420`). -/
def storageFieldSlotSpan (field : StorageFieldDecl) : Nat :=
  match field.ty with
  | .scalar (.adt _ maxFields) =>
      1 + maxFields
  | .scalar (.fixedArray (.uintN 128) size) =>
      (size + 1) / 2
  | .scalar (.fixedArray elemTy size) =>
      ((fixedArrayElementWordStride? elemTy).getD 1) * size
  | _ =>
      1

/-- Next available storage slot watermark after all persistent fields in `fields` (`#2420`). -/
def contractStorageSlotWatermark (fields : Array StorageFieldDecl) : Nat :=
  fields.foldl
    (fun acc field =>
      if field.isTransient then acc
      else max acc (field.slotNum + storageFieldSlotSpan field))
    0

/-- Shift a `StorageFieldDecl` by `slotOffset` (and optional ERC-7201 `namespaceRoot?`)
    modulo `Compiler.Constants.evmModulus` (`#2420`). -/
def offsetInheritedStorageField
    (slotOffset : Nat)
    (namespaceRoot? : Option Nat := none)
    (field : StorageFieldDecl) : StorageFieldDecl :=
  applyStorageFieldRelativeOffset slotOffset namespaceRoot? field

/-- Recursively shift all leaf slot indices in a `StorageAccessorTree` by `slotOffset` (`#2420`). -/
partial def offsetInheritedStorageAccessorTree
    (slotOffset : Nat)
    (namespaceRoot? : Option Nat := none) :
    StorageAccessorTree → StorageAccessorTree
  | .leaf name ty slotNum =>
      let rel : Compiler.CompilationModel.RelativeSlotOffset :=
        { namespaceRoot? := namespaceRoot?
          parentSlotOffset := slotOffset
          localSlot := slotNum }
      .leaf name ty rel.resolvedSlot
  | .node name children =>
      .node name (children.map (offsetInheritedStorageAccessorTree slotOffset namespaceRoot?))

/-- Shift a `StorageStructAccessorDecl` by `slotOffset` (`#2420`). -/
def offsetInheritedStorageStructAccessor
    (slotOffset : Nat)
    (namespaceRoot? : Option Nat := none)
    (decl : StorageStructAccessorDecl) : StorageStructAccessorDecl :=
  { decl with tree := offsetInheritedStorageAccessorTree slotOffset namespaceRoot? decl.tree }

/-- Check whether two `StorageFieldDecl` entries collide in the same storage space
    (same `isTransient` flag, overlapping slot range, and non-disjoint `packedBits`). -/
def storageFieldsCollide (a b : StorageFieldDecl) : Bool :=
  if a.isTransient != b.isTransient then
    false
  else
    let aStart := a.slotNum
    let aEnd := aStart + storageFieldSlotSpan a
    let bStart := b.slotNum
    let bEnd := bStart + storageFieldSlotSpan b
    let slotsOverlap := decide (aStart < bEnd ∧ bStart < aEnd)
    if !slotsOverlap then
      false
    else
      match a.packedBits, b.packedBits with
      | some (offA, widA), some (offB, widB) =>
          decide (a.slotNum == b.slotNum) &&
            !Compiler.CompilationModel.PackedBits.disjoint
              { offset := offA, width := widA }
              { offset := offB, width := widB }
      | _, _ => true

/-- Find the first storage slot collision between `parentFields` and `childFields`,
    returning `some (collidingSlot, parentFieldName, childFieldName)` when found (`#2420`). -/
def detectInheritedSlotCollision?
    (parentFields childFields : Array StorageFieldDecl) :
    Option (Nat × String × String) := Id.run do
  for cField in childFields do
    for pField in parentFields do
      if storageFieldsCollide pField cField then
        return some (cField.slotNum, pField.name, cField.name)
  return none

/-- Compose `parentFields` and `childFields` into a flattened inheritance storage layout.
    When `offsetChildByWatermark = true`, every child field is shifted by the parent's
    storage watermark (`contractStorageSlotWatermark parentFields`) so relative child
    slots `0, 1, ...` never collide with ancestor slots (`#2420`). -/
def composeInheritedStorageLayout
    (parentFields childFields : Array StorageFieldDecl)
    (offsetChildByWatermark : Bool := false)
    (namespaceRoot? : Option Nat := none) :
    Array StorageFieldDecl × Nat :=
  let watermark := contractStorageSlotWatermark parentFields
  let effectiveChild :=
    if offsetChildByWatermark then
      childFields.map (offsetInheritedStorageField watermark namespaceRoot?)
    else
      childFields
  (parentFields ++ effectiveChild, watermark)

/-! ## 2. Child-Scope `override` Method Resolution (`#2419`) -/

/-- Canonical dispatch signature key `(methodName, paramTypes)` for inheritance
    and overload resolution (`#2419`). -/
def inheritanceSignatureKey (fn : FunctionDecl) : String × List ValueType :=
  (fn.name, fn.params.toList.map (·.ty))

/-- Canonical internal helper name for a parent method retained when overridden
    by a child contract (`__super_<ParentName>_<methodName>`), enabling `super.f(args)` (`#2419`). -/
def superMethodMangledName (parentName methodName : String) : String :=
  s!"__super_{parentName}_{methodName}"

/-- Validate that `childFn` is a legal Solidity override of `inheritedFn` (`#2419`). -/
def validateMethodOverride
    (inheritedFn childFn : FunctionDecl) : Except String Unit := do
  if !inheritedFn.isVirtual then
    throw s!"function '{childFn.name}' overrides a non-virtual inherited function"
  if !inheritedFn.isPayable && childFn.isPayable then
    throw s!"function '{childFn.name}' cannot widen a nonpayable inherited function to payable"
  if inheritedFn.isPayable && !childFn.isPayable then
    throw s!"function '{childFn.name}' cannot change an inherited payable function to nonpayable"
  if inheritedFn.isPure && !childFn.isPure then
    throw s!"function '{childFn.name}' cannot weaken an inherited pure function"
  if inheritedFn.isView && !childFn.isView && !childFn.isPure then
    throw s!"function '{childFn.name}' cannot weaken an inherited view function to state-mutating"
  if inheritedFn.isInternal != childFn.isInternal then
    throw s!"function '{childFn.name}' must preserve inherited internal/external visibility"
  if inheritedFn.returnTy != childFn.returnTy then
    throw s!"function '{childFn.name}' must preserve the inherited return type"
  pure ()

/-- Convert an overridden parent `FunctionDecl` into a retained internal helper
    declaration callable via `super.<method>(args)` (`#2419`). -/
def mkRetainedSuperFunctionDecl
    (parentName : String) (inheritedFn : FunctionDecl) : FunctionDecl :=
  let mangled := superMethodMangledName parentName inheritedFn.name
  { inheritedFn with
    ident := mkIdentFrom inheritedFn.ident (Name.mkSimple mangled)
    name := mangled
    isInternal := true
    isVirtual := false
    isOverride := false }

/-- Result of resolving a child contract's methods against an inherited parent method table (`#2419`). -/
structure ResolvedInheritanceMethods where
  /-- Effective method dispatch table (with overridden parent methods replaced by child methods). -/
  effectiveFunctions : Array FunctionDecl
  /-- Retained parent method implementations (`(parentName, originalMethodName, mangledDecl)`)
      available for `super.f(args)` calls inside the child contract. -/
  retainedSuperFunctions : Array (String × String × FunctionDecl)

/-- Resolve `childFns` against `parentFns` from `parentName`, validating `override`
    and `virtual` rules and retaining overridden parent bodies for `super.f(args)` (`#2419`). -/
def resolveChildOverrideMethods
    (parentName : String)
    (parentFns childFns : Array FunctionDecl) :
    Except String ResolvedInheritanceMethods := Id.run do
  let mut functions := parentFns
  let mut retainedSupers : Array (String × String × FunctionDecl) := #[]
  for fn in childFns do
    let key := inheritanceSignatureKey fn
    let inherited? := functions.find? (fun candidate => inheritanceSignatureKey candidate == key)
    match fn.isOverride, inherited? with
    | true, none =>
        return .error
          s!"function '{fn.name}' is marked override, but no inherited function has the same signature"
    | true, some inherited =>
        match validateMethodOverride inherited fn with
        | .error err => return .error err
        | .ok () =>
            let superDecl := mkRetainedSuperFunctionDecl parentName inherited
            retainedSupers := retainedSupers.push (parentName, inherited.name, superDecl)
            functions := functions.map fun candidate =>
              if inheritanceSignatureKey candidate == key then
                { fn with isOverride := false }
              else
                candidate
    | false, some _ =>
        return .error
          s!"function '{fn.name}' has the same signature as an inherited function; add override (the inherited function must be virtual)"
    | false, none =>
        functions := functions.push fn
  return .ok
    { effectiveFunctions := functions
      retainedSuperFunctions := retainedSupers }

/-! ## 3. `super.f(args)` Call Resolution (`#2419`) -/

/-- Resolved target of a `super.f(args)` call in a child contract (`#2419`). -/
structure SuperCallTarget where
  parentName : String
  methodName : String
  mangledHelperName : String
  decl : FunctionDecl

/-- Resolve `super.<methodName>` along the linearized parent chain `linearizedParents`
    (ordered from most-derived parent to base-most ancestor, matching Solidity C3 `super`
    lookup). When `argCount?` is supplied, only methods with matching arity are considered (`#2419`). -/
def resolveSuperCallTarget?
    (linearizedParents : Array (String × Array FunctionDecl))
    (methodName : String)
    (argCount? : Option Nat := none) : Option SuperCallTarget := Id.run do
  for (parentName, parentFns) in linearizedParents do
    let found? := parentFns.find? fun fn =>
      fn.name == methodName &&
        match argCount? with
        | some n => fn.params.size == n
        | none => true
    if let some decl := found? then
      return some
        { parentName := parentName
          methodName := methodName
          mangledHelperName := superMethodMangledName parentName methodName
          decl := decl }
  return none

/-- Recognize `super.<method>(args...)` or `super.<method>` syntax in an expression term,
    returning `some (methodName, args)` when matched (`#2419`). -/
def parseSuperCallSyntax? (stx : Term) : Option (String × Array Term) :=
  let raw := (stripParens stx).raw
  if raw.getKind == `Lean.Parser.Term.app then
    let head := raw[0]
    let args := raw[1].getArgs.map (fun a => (⟨a⟩ : Term))
    match head with
    | .ident _ _ (.str (.str .anonymous "super") methodName) _ =>
        some (methodName, args)
    | _ =>
        if head.getKind == `Lean.Parser.Term.proj then
          match head[0], head[2] with
          | .ident _ _ (.str .anonymous "super") _, .ident _ _ (.str .anonymous methodName) _ =>
              some (methodName, args)
          | _, _ => none
        else
          none
  else
    match raw with
    | .ident _ _ (.str (.str .anonymous "super") methodName) _ =>
        some (methodName, #[])
    | _ =>
        if raw.getKind == `Lean.Parser.Term.proj then
          match raw[0], raw[2] with
          | .ident _ _ (.str .anonymous "super") _, .ident _ _ (.str .anonymous methodName) _ =>
              some (methodName, #[])
          | _, _ => none
        else
          none

/-- Rewrite a `super.f(args)` term into an internal helper call to the resolved
    mangled ancestor implementation `__super_<Parent>_<f> args*` (`#2419`). -/
def rewriteSuperCallTerm
    (linearizedParents : Array (String × Array FunctionDecl))
    (stx : Term) : CommandElabM Term := do
  match parseSuperCallSyntax? stx with
  | none => pure stx
  | some (methodName, args) =>
      let some target := resolveSuperCallTarget? linearizedParents methodName (some args.size)
        | throwErrorAt stx
            s!"unresolved super call 'super.{methodName}' with {args.size} argument(s); no matching ancestor method found"
      let helperIdent := mkIdentFrom stx (Name.mkSimple target.mangledHelperName)
      if args.isEmpty then
        `($helperIdent ())
      else
        `($helperIdent $args*)

end Verity.Macro
