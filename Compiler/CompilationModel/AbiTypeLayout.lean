import Compiler.CompilationModel.Types

namespace Compiler.CompilationModel

-- Whether an ABI param type is dynamically sized (requires offset-based encoding).
-- Used by both event encoding and calldata parameter loading.
mutual
  def isDynamicParamType : ParamType → Bool
    | ParamType.uint256 => false
    | ParamType.int256 => false
    | ParamType.uint8 => false
    | ParamType.uint16 => false
    | ParamType.uintN _ | ParamType.intN _ | ParamType.bytesN _ => false
    | ParamType.address => false
    | ParamType.bool => false
    | ParamType.bytes32 => false
    | ParamType.string => true
    | ParamType.array _ => true
    | ParamType.bytes => true
    | ParamType.fixedArray elemTy _ => isDynamicParamType elemTy
    | ParamType.tuple elemTys => isDynamicParamTypeList elemTys
    | ParamType.adt _ _ => false  -- ADTs are statically-sized tagged unions
    | ParamType.newtypeOf _ baseType => isDynamicParamType baseType  -- Erased to base type
  termination_by ty => sizeOf ty

  def isDynamicParamTypeList : List ParamType → Bool
    | [] => false
    | ty :: rest => isDynamicParamType ty || isDynamicParamTypeList rest
  termination_by tys => sizeOf tys
end

-- ABI head size in bytes for a param type. Dynamic types occupy one 32-byte
-- offset word; static composites are the sum of their element head sizes.
-- Used by both event encoding and calldata parameter loading.
mutual
  def paramHeadSize : ParamType → Nat
    | ParamType.uint256 => 32
    | ParamType.int256 => 32
    | ParamType.uint8 => 32
    | ParamType.uint16 => 32
    | ParamType.uintN _ | ParamType.intN _ | ParamType.bytesN _ => 32
    | ParamType.address => 32
    | ParamType.bool => 32
    | ParamType.bytes32 => 32
    | ParamType.string => 32
    | ParamType.array _ => 32
    | ParamType.bytes => 32
    | ParamType.fixedArray elemTy n =>
        if isDynamicParamType elemTy then 32 else n * paramHeadSize elemTy
    | ParamType.tuple elemTys =>
        if isDynamicParamTypeList elemTys then 32 else paramHeadSizeList elemTys
    | ParamType.adt _ maxFields => 32 * (1 + maxFields)  -- ADTs: uint8 tag word + maxFields field words (#1727 Step 5e)
    | ParamType.newtypeOf _ baseType => paramHeadSize baseType  -- Erased to base type
  termination_by ty => sizeOf ty

  def paramHeadSizeList : List ParamType → Nat
    | [] => 0
    | ty :: rest => paramHeadSize ty + paramHeadSizeList rest
  termination_by tys => sizeOf tys
end

def eventIsDynamicType := isDynamicParamType

def eventHeadWordSize := paramHeadSize

mutual
  /-- Number of 32-byte words an ABI value contributes to its parent's head.
  Dynamic children occupy one offset word in the parent head. -/
  partial def paramParentHeadWords : ParamType → Nat
    | ParamType.string | ParamType.bytes | ParamType.array _ => 1
    | ParamType.tuple elemTys =>
        if isDynamicParamTypeList elemTys then 1 else paramLocalHeadWords (ParamType.tuple elemTys)
    | ParamType.fixedArray elemTy n =>
        if isDynamicParamType (ParamType.fixedArray elemTy n) then 1 else n * paramParentHeadWords elemTy
    | ParamType.newtypeOf _ baseType => paramParentHeadWords baseType
    | ParamType.uint256 | ParamType.int256 | ParamType.uint8 | ParamType.uint16
    | ParamType.uintN _ | ParamType.intN _ | ParamType.bytesN _ | ParamType.address
    | ParamType.bool | ParamType.bytes32 => 1
    | ParamType.adt _ maxFields => 1 + maxFields

  /-- Number of 32-byte words in the local head of an ABI value once its dynamic
  tail has been entered. Dynamic children occupy one offset word in that head. -/
  partial def paramLocalHeadWords : ParamType → Nat
    | ParamType.uint256 | ParamType.int256 | ParamType.uint8 | ParamType.uint16
    | ParamType.uintN _ | ParamType.intN _ | ParamType.bytesN _ | ParamType.address
    | ParamType.bool | ParamType.bytes32 | ParamType.string | ParamType.bytes
    | ParamType.array _ => 1
    | ParamType.fixedArray elemTy n => n * paramParentHeadWords elemTy
    | ParamType.tuple elemTys => elemTys.foldl (fun acc ty => acc + paramParentHeadWords ty) 0
    | ParamType.adt _ maxFields => 1 + maxFields
    | ParamType.newtypeOf _ baseType => paramLocalHeadWords baseType
end

/-- Whether a parameter type is ABI-encoded as exactly one 32-byte word without
needing offset-based dynamic handling. -/
def isSingleWordStaticParamType (ty : ParamType) : Bool :=
  !isDynamicParamType ty && paramHeadSize ty == 32

/-- Dynamic array parameters whose elements can be copied/read word-for-word. -/
def isWordArrayParam : ParamType → Bool
  | ParamType.array elemTy => isSingleWordStaticParamType elemTy
  | _ => false

/-- Whether the dynamic param shape is length-prefixed in the ABI tail.
    Dynamic arrays (`T[]`), `bytes`, and `string` all begin with a 32-byte
    length word followed by data. Dynamic tuples (structs containing nested
    dynamic members) do not — their offset pointer dereferences directly
    to the first head word of the tuple's encoding. (verity#1839)

Lives here rather than beside the calldata loader so the ABI model
(`Verity/Core/Model/DynamicAbi.lean`) and the Yul emitter can share one
definition (verity#2085). -/
def isLengthPrefixedDynamicShape : ParamType → Bool
  | ParamType.bytes | ParamType.string | ParamType.array _ => true
  | _ => false

/-- Number of 32-byte words one element of a dynamic array occupies in the
array's tail.  A dynamically sized element contributes a single offset word to
the array's own head area; a static element contributes its whole head.

Lives here rather than beside the calldata loader so the ABI model
(`Verity/Core/Model/DynamicAbi.lean`) and the Yul emitter can share one
definition: the emitted `div` bound and the model's `fitsLength` bound are then
the same number by construction rather than by a restated case list
(verity#2085). -/
def dynamicArrayElementStrideWords (elemTy : ParamType) : Nat :=
  if isDynamicParamType elemTy then
    1
  else
    max 1 (paramHeadSize elemTy / 32)

theorem dynamicArrayElementStrideWords_pos (elemTy : ParamType) :
    0 < dynamicArrayElementStrideWords elemTy := by
  unfold dynamicArrayElementStrideWords
  split <;> omega

@[simp] theorem max_one_dynamicArrayElementStrideWords (elemTy : ParamType) :
    Nat.max 1 (dynamicArrayElementStrideWords elemTy) = dynamicArrayElementStrideWords elemTy :=
  Nat.max_eq_right (dynamicArrayElementStrideWords_pos elemTy)

end Compiler.CompilationModel
