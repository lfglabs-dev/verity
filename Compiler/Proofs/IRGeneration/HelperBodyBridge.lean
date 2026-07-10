import Compiler.CompilationModel.Compile
import Compiler.Proofs.IRGeneration.SupportedSpec

namespace Compiler.Proofs.IRGeneration

open Compiler.CompilationModel

mutual

/-- Sufficient syntactic exclusion for statement forms whose compilation can
depend on internal-return targets.  This intentionally follows the conservative
shape of `stmtTouchesUnsupportedHelperSurface`: unsupported wrappers and ADT
matches are rejected at the head instead of recursively inspected. -/
def stmtUsesReturnFamily : Stmt → Bool
  | .return _ | .returnValues _ | .returnArray _ | .returnBytes _
  | .returnStorageWords _ | .returnCodeData _ => true
  | .unsafeBlock _ _ | .unsafeYul _ | .matchAdt _ _ _ => true
  | .ite _ thenBranch elseBranch =>
      stmtListUsesReturnFamily thenBranch ||
        stmtListUsesReturnFamily elseBranch
  | .forEach _ _ body | .forEachSetBit _ _ body =>
      stmtListUsesReturnFamily body
  | _ => false

/-- List form of `stmtUsesReturnFamily`. -/
def stmtListUsesReturnFamily : List Stmt → Bool
  | [] => false
  | stmt :: rest =>
      stmtUsesReturnFamily stmt ||
        stmtListUsesReturnFamily rest

end

mutual

/-- Sufficient syntactic exclusion for helper bodies that can halt the caller via
source-level `Stmt.stop`.  Conservative unsupported wrappers are rejected at the
head, matching `stmtUsesReturnFamily`. -/
def stmtUsesStop : Stmt → Bool
  | .stop => true
  | .unsafeBlock _ _ | .unsafeYul _ | .matchAdt _ _ _ => true
  | .ite _ thenBranch elseBranch =>
      stmtListUsesStop thenBranch ||
        stmtListUsesStop elseBranch
  | .forEach _ _ body | .forEachSetBit _ _ body =>
      stmtListUsesStop body
  | _ => false

/-- List form of `stmtUsesStop`. -/
def stmtListUsesStop : List Stmt → Bool
  | [] => false
  | stmt :: rest =>
      stmtUsesStop stmt ||
        stmtListUsesStop rest

end

end Compiler.Proofs.IRGeneration
