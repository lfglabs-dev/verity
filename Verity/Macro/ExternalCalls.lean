import Lean
import Verity.Macro.Syntax
import Verity.Macro.Types

namespace Verity.Macro

open Lean
open Lean.Elab.Command

def parseExternalLinkMode (stx : Syntax) : CommandElabM Compiler.CompilationModel.ForeignLinkMode := do
  match stx with
  | `(verityExternalLinkMode| external) => pure .external
  | `(verityExternalLinkMode| internal_yul) => pure .objectLinked
  | `(verityExternalLinkMode| object_linked) => pure .objectLinked
  | `(verityExternalLinkMode| inline) => pure .inline
  | `(verityExternalLinkMode| compiler_runtime) => pure .compilerRuntime
  | _ =>
      throwErrorAt stx
        "unsupported linked_as mode; expected external, internal_yul, object_linked, inline, or compiler_runtime"

def parseExternal
    (newtypes : Array NewtypeDecl)
    (structDecls : Array StructDecl)
    (adtDecls : Array AdtDecl)
    (stx : Syntax) : CommandElabM ExternalDecl := do
  match stx with
  | `(verityExternal| external $name:ident ($[$params:term],*) -> ($[$returnTys:term],*) linked_as := $mode:verityExternalLinkMode) =>
      pure {
        ident := name
        name := toString name.getId
        params := ← params.mapM (valueTypeFromSyntax newtypes structDecls adtDecls)
        returnTys := ← returnTys.mapM (valueTypeFromSyntax newtypes structDecls adtDecls)
        linkMode := ← parseExternalLinkMode mode
      }
  | `(verityExternal| external $name:ident ($[$params:term],*) linked_as := $mode:verityExternalLinkMode) =>
      pure {
        ident := name
        name := toString name.getId
        params := ← params.mapM (valueTypeFromSyntax newtypes structDecls adtDecls)
        returnTys := #[]
        linkMode := ← parseExternalLinkMode mode
      }
  | `(verityExternal| external $name:ident ($[$params:term],*) -> ($[$returnTys:term],*)) =>
      pure {
        ident := name
        name := toString name.getId
        params := ← params.mapM (valueTypeFromSyntax newtypes structDecls adtDecls)
        returnTys := ← returnTys.mapM (valueTypeFromSyntax newtypes structDecls adtDecls)
      }
  | `(verityExternal| external $name:ident ($[$params:term],*)) =>
      pure {
        ident := name
        name := toString name.getId
        params := ← params.mapM (valueTypeFromSyntax newtypes structDecls adtDecls)
        returnTys := #[]
      }
  | _ => throwErrorAt stx "invalid external declaration"

private def externalExecutableWordType? : ValueType → Bool
  | .uint256 | .int256 | .uint8 | .uint16 | .uintN _ | .intN _ | .bytesN _
  | .address | .bytes32 | .bool => true
  | .enum _ _ => true
  | .newtype _ baseType => externalExecutableWordType? baseType
  | _ => false

private def externalExecutableParamType? : ValueType → Bool
  | .array elemTy => externalExecutableWordType? elemTy
  | .bytes | .string => true
  | .newtype _ baseType => externalExecutableParamType? baseType
  | ty => externalExecutableWordType? ty

private partial def externalExecutableReturnType? : ValueType → Bool
  | .tuple elemTys => elemTys.all externalExecutableReturnType?
  | .fixedArray elemTy _ => externalExecutableReturnType? elemTy
  | .struct _ fields => fields.all (fun field => externalExecutableReturnType? field.snd)
  | .newtype _ baseType => externalExecutableReturnType? baseType
  | ty => externalExecutableWordType? ty

def validateExternalExecutableType
    (extIdent : Ident)
    (extName : String)
    (ty : ValueType)
    (role : String) : CommandElabM Unit := do
  if !externalExecutableReturnType? ty then
    throwErrorAt extIdent
      s!"linked external '{extName}' uses unsupported {role} type; executable externalCall currently supports only word-like values and static ABI composites of word-like values"

def validateExternalExecutableParamType
    (extIdent : Ident)
    (extName : String)
    (ty : ValueType) : CommandElabM Unit := do
  if !externalExecutableParamType? ty then
    throwErrorAt extIdent
      s!"linked external '{extName}' uses unsupported parameter type; executable externalCall currently supports word-like values plus direct Array<word-like>, Bytes, and String calldata parameters"

end Verity.Macro
