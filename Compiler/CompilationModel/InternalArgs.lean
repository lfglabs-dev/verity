import Compiler.CompilationModel.Types
import Compiler.CompilationModel.AbiTypeLayout

namespace Compiler.CompilationModel

partial def staticParamBindingNames (name : String) (ty : ParamType) : List String :=
  match ty with
  | ParamType.uint256 | ParamType.int256 | ParamType.uint8 | ParamType.uint16
  | ParamType.address | ParamType.bool | ParamType.bytes32 =>
      [name]
  | ParamType.fixedArray elemTy n =>
      (List.range n).flatMap (fun i => staticParamBindingNames s!"{name}_{i}" elemTy)
  | ParamType.tuple elemTys =>
      let rec go (tys : List ParamType) (idx : Nat) : List String :=
        match tys with
        | [] => []
        | elemTy :: rest =>
            staticParamBindingNames s!"{name}_{idx}" elemTy ++ go rest (idx + 1)
      go elemTys 0
  | ParamType.adt _ maxFields =>
      name :: (List.range maxFields).map (fun i => s!"{name}_f{i}")
  | ParamType.newtypeOf _ baseType =>
      staticParamBindingNames name baseType
  | _ => []

def dynamicParamBindingNames (name : String) : List String :=
  [s!"{name}_offset", s!"{name}_length", s!"{name}_data_offset"]

def internalFunctionYulParamNames (params : List Param) : List String :=
  params.flatMap fun param =>
    match param.ty with
    | ParamType.array _ =>
        [s!"{param.name}_data_offset", s!"{param.name}_length"]
    | ParamType.bytes | ParamType.string =>
        [s!"{param.name}_data_offset", s!"{param.name}_length"]
    | ParamType.fixedArray _ _ =>
        if isDynamicParamType param.ty then
          [s!"{param.name}_data_offset"]
        else
          staticParamBindingNames param.name param.ty
    | ParamType.tuple _ =>
        if isDynamicParamType param.ty then
          [s!"{param.name}_data_offset"]
        else
          staticParamBindingNames param.name param.ty
    | ParamType.newtypeOf _ baseTy =>
        if isDynamicParamType param.ty then
          [s!"{param.name}_data_offset"]
        else
          staticParamBindingNames param.name baseTy
    | ParamType.adt _ _ =>
        staticParamBindingNames param.name param.ty
    | _ => [param.name]

def internalCallYulArgNamesForBase (name : String) : ParamType → List String
  | ParamType.array _ => [s!"{name}_data_offset", s!"{name}_length"]
  | ParamType.bytes | ParamType.string => [s!"{name}_data_offset", s!"{name}_length"]
  | ty@(ParamType.fixedArray _ _) =>
      if isDynamicParamType ty then [s!"{name}_data_offset"] else staticParamBindingNames name ty
  | ty@(ParamType.tuple _) =>
      if isDynamicParamType ty then [s!"{name}_data_offset"] else staticParamBindingNames name ty
  | ParamType.newtypeOf _ baseTy => internalCallYulArgNamesForBase name baseTy
  | ty@(ParamType.adt _ _) => staticParamBindingNames name ty
  | _ => [name]

def internalCallYulArgNamesForParam (sourceName : String) (param : Param) : List String :=
  match param.ty with
  | ParamType.adt _ _ => staticParamBindingNames sourceName param.ty
  | _ => internalCallYulArgNamesForBase sourceName param.ty

def isExpandedInternalParamType : ParamType → Bool
  | ParamType.array _ | ParamType.bytes | ParamType.string => true
  | ParamType.fixedArray _ _ | ParamType.tuple _ => true
  | ParamType.newtypeOf _ baseTy => isExpandedInternalParamType baseTy
  | ParamType.adt _ _ => true
  | _ => false

end Compiler.CompilationModel
