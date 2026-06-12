/-
  Compatibility shim: the declarative model types moved to the compiler-free
  core module `Verity.Core.Model.Types` (#1313). This file keeps the historic
  import path alive and holds the IR-facing projections, which are the only
  parts of the old module that depend on `Compiler.IR`.
-/

import Verity.Core.Model.Types
import Compiler.IR

namespace Compiler.CompilationModel

def ParamType.toIRType : ParamType → IRType
  | uint256 => IRType.uint256
  | int256 => IRType.uint256
  | uint8 => IRType.uint256
  | uint16 => IRType.uint256
  | address => IRType.address
  | bool => IRType.uint256
  | bytes32 => IRType.uint256  -- bytes32 is a 256-bit value
  | string => IRType.uint256
  | tuple _ => IRType.uint256  -- Tuples are represented as ABI offsets for now
  | array _ => IRType.uint256  -- Arrays are represented as calldata offsets
  | fixedArray _ _ => IRType.uint256
  | bytes => IRType.uint256
  | adt _ _ => IRType.uint256  -- ADTs are represented as storage offsets
  | newtypeOf _ baseType => baseType.toIRType  -- Erased to base type

def Param.toIRParam (p : Param) : IRParam :=
  { name := p.name, ty := p.ty.toIRType }

end Compiler.CompilationModel
