/-
  Compiler.Linker: External Yul Library Linking

  This module provides functionality to link external Yul library files
  with generated contract code, enabling production cryptographic libraries
  to be used with formally verified contract logic.

  Usage:
    lake exe verity-compiler \
        --link examples/external-libs/PoseidonT3.yul \
        --link examples/external-libs/PoseidonT4.yul \
        -o artifacts/yul
-/

import Compiler.Yul.Ast
import Compiler.Yul.PrettyPrint

namespace Compiler.Linker

open Compiler.Yul

/-!
## Yul Library Parsing

External libraries are expected to contain pure Yul function definitions.
We use a simple line-based parser to extract function definitions from library files.
-/

-- Extract function name from a Yul function definition line
private def extractFunctionName (line : String) : Option String :=
  let trimmed := line.trim
  if trimmed.startsWith "function " then
    let afterFunction := trimmed.drop "function ".length
    let beforeParen := afterFunction.takeWhile (· != '(')
    some beforeParen.trim
  else
    none

-- Extract parameter count from a Yul function definition line
-- e.g. "function foo(a, b) -> result {" has arity 2
private def extractFunctionArity (line : String) : Nat :=
  let trimmed := line.trim
  -- Find the parameter list between '(' and ')'
  match trimmed.posOf '(', trimmed.posOf ')' with
  | openPos, closePos =>
    if openPos < closePos then
      let params := (trimmed.extract ⟨openPos.byteIdx + 1⟩ closePos).trim
      if params.isEmpty then 0
      else (params.splitOn ",").length
    else 0

-- Check if a line starts a function definition
private def isFunctionStart (line : String) : Bool :=
  extractFunctionName line |>.isSome

-- Stateful scanner used to ignore braces inside comments/strings.
private structure ScanState where
  inBlockComment : Bool := false
  inString : Option Char := none
  escaped : Bool := false
  deriving Repr

-- Count braces in a line while ignoring comment and string contexts.
private def countBracesWithState (state : ScanState) (line : String) : Int × ScanState :=
  let rec go : Nat → List Char → Int → ScanState → Int × ScanState
    | 0, _, delta, st =>
        let st' := { st with escaped := false }
        (delta, st')
    | _ + 1, [], delta, st =>
        let st' := { st with escaped := false }
        (delta, st')
    | fuel + 1, c :: cs, delta, st =>
        if st.inBlockComment then
          match c, cs with
          | '*', '/' :: rest => go fuel rest delta { st with inBlockComment := false, escaped := false }
          | _, _ => go fuel cs delta st
        else
          match st.inString with
          | some quote =>
              if st.escaped then
                go fuel cs delta { st with escaped := false }
              else if c == '\\' then
                go fuel cs delta { st with escaped := true }
              else if c == quote then
                go fuel cs delta { st with inString := none, escaped := false }
              else
                go fuel cs delta st
          | none =>
              match c, cs with
              | '/', '/' :: _ =>
                  -- Line comment: ignore rest of this line.
                  (delta, st)
              | '/', '*' :: rest =>
                  go fuel rest delta { st with inBlockComment := true, escaped := false }
              | '"', _ =>
                  go fuel cs delta { st with inString := some '"', escaped := false }
              | '\'', _ =>
                  go fuel cs delta { st with inString := some '\'', escaped := false }
              | '{', _ =>
                  go fuel cs (delta + 1) st
              | '}', _ =>
                  go fuel cs (delta - 1) st
              | _, _ =>
                  go fuel cs delta st
  go line.length line.toList 0 state

-- Extract a complete function definition from lines
private def extractFunction (lines : List String) : Option (String × List String × List String) :=
  match lines with
  | [] => none
  | firstLine :: rest =>
      match extractFunctionName firstLine with
      | none => none
      | some name =>
          let rec collectBody (remaining : List String) (acc : List String) (depth : Int) (state : ScanState) : List String × List String :=
            match remaining with
            | [] => (acc.reverse, [])
            | line :: rest' =>
                let (delta, state') := countBracesWithState state line
                let newDepth := depth + delta
                let acc' := line :: acc
                if newDepth <= 0 then
                  (acc'.reverse, rest')
                else
                  collectBody rest' acc' newDepth state'
          let (initialDelta, initialState) := countBracesWithState {} firstLine
          let (bodyLines, remaining) := collectBody rest [firstLine] initialDelta initialState
          some (name, bodyLines, remaining)

-- Extract all function definitions from library lines
-- Uses fuel bounded by line count to guarantee termination
private def extractAllFunctions (lines : List String) : List (String × List String) :=
  go lines [] lines.length
where
  go (remaining : List String) (acc : List (String × List String)) (fuel : Nat) : List (String × List String) :=
    match fuel with
    | 0 => acc.reverse
    | fuel' + 1 =>
      match remaining with
      | [] => acc.reverse
      | line :: rest =>
          if isFunctionStart line then
            match extractFunction (line :: rest) with
            | none => go rest acc fuel'
            | some (name, body, remaining') =>
                go remaining' ((name, body) :: acc) fuel'
          else
            go rest acc fuel'

/-!
## Library Loading
-/

structure LibraryFunction where
  name : String
  arity : Nat         -- Number of parameters
  body : List String  -- Raw Yul text lines
  deriving Repr

-- Parse a Yul library file and extract function definitions
def parseLibrary (content : String) : List LibraryFunction :=
  let lines := content.splitOn "\n"
  let functions := extractAllFunctions lines
  functions.map fun (name, body) =>
    let arity := match body.head? with
      | some firstLine => extractFunctionArity firstLine
      | none => 0
    { name := name, arity := arity, body := body }

-- Load library from file path
def loadLibrary (path : String) : IO (List LibraryFunction) := do
  let content ← IO.FS.readFile path
  return parseLibrary content

/-!
## Linking

**Note**: Library functions are injected at text level, not AST level.
This is a known limitation (see issue #173). The formal proofs do not
cover linked library code - this is a trust assumption documented in
`TRUST_ASSUMPTIONS.md`.
-/

-- Indentation level for library functions in runtime code (3 levels × 4 spaces = 12 spaces)
private def libraryIndent : String := "            "

-- Inject library function text directly into rendered Yul output
-- This preserves the exact library code without parsing/re-emitting
-- Returns an error if the runtime code injection site is not found.
def renderWithLibraries (obj : YulObject) (libraries : List LibraryFunction) : Except String String :=
  -- Render the main object
  let mainYul := Yul.render obj

  -- If no libraries, return as-is
  if libraries.isEmpty then
    .ok mainYul
  else
    -- Extract the runtime code section and inject libraries
    -- Find the runtime "code {" line and inject library functions after it
    let lines := mainYul.splitOn "\n"
    let rec insertLibraries (remaining : List String) (acc : List String) (inserted : Bool) (depth : Nat) : List String × Bool :=
      match remaining with
      | [] => (acc, inserted)
      | line :: rest =>
          -- Track depth: we want the second "code {" (inside object "runtime")
          let isCodeLine := line.trim.startsWith "code {"
          let newDepth := if isCodeLine then depth + 1 else depth
          if !inserted && newDepth == 2 && isCodeLine then
            -- Found the runtime code section, insert libraries after this line
            let libraryLines := libraries.flatMap fun fn =>
              -- Add proper indentation for runtime code functions
              fn.body.map fun bodyLine =>
                if bodyLine.trim.isEmpty then bodyLine
                else libraryIndent ++ bodyLine
            insertLibraries rest (acc ++ [line] ++ libraryLines) true newDepth
          else
            insertLibraries rest (acc ++ [line]) inserted newDepth
    let (resultLines, inserted) := insertLibraries lines [] false 0
    if !inserted then
      .error s!"Failed to find runtime code injection site in {obj.name}. Library functions could not be linked."
    else
      .ok (String.intercalate "\n" resultLines)

/-!
## Validation
-/

-- EVM/Yul built-in opcodes (not user-defined functions).
-- This list must include all opcodes that linked libraries may call,
-- otherwise `validateExternalReferences` will reject valid library code.
-- Keep in sync with `interopBuiltinCallNames` in ContractSpec.lean.
private def yulBuiltins : List String :=
  ["add", "sub", "mul", "div", "sdiv", "mod", "smod", "exp",
   "not", "lt", "gt", "slt", "sgt", "eq", "iszero", "and", "or", "xor",
   "byte", "shl", "shr", "sar", "addmod", "mulmod", "signextend",
   "keccak256",
   "address", "balance", "selfbalance", "origin", "caller", "callvalue",
   "calldataload", "calldatasize", "calldatacopy", "codesize", "codecopy",
   "gasprice", "extcodesize", "extcodecopy", "returndatasize", "returndatacopy",
   "extcodehash", "blockhash", "coinbase", "timestamp", "number", "difficulty",
   "prevrandao", "gaslimit", "chainid", "basefee", "blobbasefee", "blobhash",
   "pop", "mload", "mstore", "mstore8", "sload", "sstore", "tload", "tstore",
   "mcopy", "msize", "gas", "pc",
   "log0", "log1", "log2", "log3", "log4",
   "create", "create2", "call", "callcode", "delegatecall", "staticcall",
   "return", "revert", "selfdestruct", "invalid", "stop",
   "datasize", "dataoffset", "datacopy"]

private def isYulBuiltinCall (name : String) : Bool :=
  yulBuiltins.contains name || name.startsWith "verbatim_"

-- Collect all function definitions from Yul statements
mutual
private def defsFromStmt : YulStmt → List String
  | YulStmt.funcDef name _ _ body => name :: defsFromStmts body
  | YulStmt.if_ _ body => defsFromStmts body
  | YulStmt.for_ init _ post body =>
      defsFromStmts init ++ defsFromStmts post ++ defsFromStmts body
  | YulStmt.switch _ cases defaultCase =>
      defsFromCases cases ++ defsFromDefault defaultCase
  | YulStmt.block stmts => defsFromStmts stmts
  | _ => []

private def defsFromStmts : List YulStmt → List String
  | [] => []
  | s :: ss => defsFromStmt s ++ defsFromStmts ss

private def defsFromCases : List (Nat × List YulStmt) → List String
  | [] => []
  | (_, body) :: rest => defsFromStmts body ++ defsFromCases rest

private def defsFromDefault : Option (List YulStmt) → List String
  | none => []
  | some body => defsFromStmts body
end

-- Collect all function names defined in library
private def collectLibraryFunctions (libs : List LibraryFunction) : List String :=
  libs.map (·.name)

/-- Returns the first duplicate string in traversal order, if any. -/
def findDuplicate (names : List String) : Option String :=
  let rec go : List String → List String → Option String
    | [], _ => none
    | n :: rest, seen =>
        if seen.contains n then some n
        else go rest (n :: seen)
  go names []

-- Validate that no two library functions share the same name
def validateNoDuplicateNames (libraries : List LibraryFunction) : Except String Unit := do
  let names := libraries.map (·.name)
  match findDuplicate names with
  | some dup => throw s!"Duplicate library function name: {dup}"
  | none => pure ()

-- Validate that library functions don't shadow generated code or builtins.
-- Catches bugs where a library redefines e.g. `mappingSlot` or a Yul builtin.
def validateNoNameCollisions (obj : YulObject) (libraries : List LibraryFunction) : Except String Unit := do
  let allCode := obj.deployCode ++ obj.runtimeCode
  let localDefs := (defsFromStmts allCode).eraseDups
  let libNames := collectLibraryFunctions libraries
  -- Check library names vs locally-defined functions
  let localCollisions := libNames.filter fun name => localDefs.contains name
  if !localCollisions.isEmpty then
    throw s!"Library function(s) shadow generated code: {String.intercalate ", " localCollisions}"
  -- Check library names vs Yul builtins
  let builtinCollisions := libNames.filter fun name => isYulBuiltinCall name
  if !builtinCollisions.isEmpty then
    throw s!"Library function(s) shadow Yul builtins: {String.intercalate ", " builtinCollisions}"
  pure ()

-- Collect all function calls (with argument counts) from Yul statements.
-- Also used to derive plain call names via .map Prod.fst.
mutual
private def callsWithArityFromExpr : YulExpr → List (String × Nat)
  | YulExpr.call name args => (name, args.length) :: callsWithArityFromExprs args
  | YulExpr.lit _ => []
  | YulExpr.hex _ => []
  | YulExpr.str _ => []
  | YulExpr.ident _ => []

private def callsWithArityFromExprs : List YulExpr → List (String × Nat)
  | [] => []
  | e :: es => callsWithArityFromExpr e ++ callsWithArityFromExprs es

private def callsWithArityFromStmt : YulStmt → List (String × Nat)
  | YulStmt.comment _ => []
  | YulStmt.let_ _ value => callsWithArityFromExpr value
  | YulStmt.letMany _ value => callsWithArityFromExpr value
  | YulStmt.assign _ value => callsWithArityFromExpr value
  | YulStmt.exprStmt e => callsWithArityFromExpr e
  | YulStmt.leave => []
  | YulStmt.if_ cond body => callsWithArityFromExpr cond ++ callsWithArityFromStmts body
  | YulStmt.for_ init cond post body =>
      callsWithArityFromStmts init ++ callsWithArityFromExpr cond ++
      callsWithArityFromStmts post ++ callsWithArityFromStmts body
  | YulStmt.switch expr cases defaultCase =>
      callsWithArityFromExpr expr ++
      callsWithArityCases cases ++
      callsWithArityDefault defaultCase
  | YulStmt.block stmts => callsWithArityFromStmts stmts
  | YulStmt.funcDef _ _ _ body => callsWithArityFromStmts body

private def callsWithArityFromStmts : List YulStmt → List (String × Nat)
  | [] => []
  | s :: ss => callsWithArityFromStmt s ++ callsWithArityFromStmts ss

private def callsWithArityCases : List (Nat × List YulStmt) → List (String × Nat)
  | [] => []
  | (_, body) :: rest => callsWithArityFromStmts body ++ callsWithArityCases rest

private def callsWithArityDefault : Option (List YulStmt) → List (String × Nat)
  | none => []
  | some body => callsWithArityFromStmts body
end

private def externalReferenceContext
    (obj : YulObject) (libraries : List LibraryFunction) :
    List String × List String × List String := Id.run do
  let allCode := obj.deployCode ++ obj.runtimeCode
  let allCalls := (callsWithArityFromStmts allCode |>.map Prod.fst).eraseDups
  let localDefs := (defsFromStmts allCode).eraseDups
  let providedFunctions := collectLibraryFunctions libraries
  pure (allCalls, localDefs, providedFunctions)

private def collectExternalCallNames (obj : YulObject) (libraries : List LibraryFunction) : List String :=
  let (allCalls, localDefs, providedFunctions) := externalReferenceContext obj libraries
  allCalls.filter fun call =>
    !isYulBuiltinCall call && !localDefs.contains call && providedFunctions.contains call

/-- Keep only referenced external library functions (transitive closure), preserving
    input order.
    This deterministic text-linking minimization step avoids injecting unused
    library helpers while still retaining helper dependencies needed by retained
    library functions.
    Exported for downstream compiler frontends (for example `morpho-verity`) that
    pre-filter libraries before invoking linker validation/rendering. -/
private def collectReferencedLibraryClosure
    (libraries : List LibraryFunction) (seed : List String) : List String :=
  let providedFunctions := collectLibraryFunctions libraries
  let referencesFunctionName := fun (body : List String) (name : String) =>
    let text := String.intercalate "\n" body
    (text.splitOn s!"{name}(").length > 1
  let callNamesInLibraryBody := fun (body : List String) =>
    providedFunctions.filter (fun name => referencesFunctionName body name)
  let rec expand (fuel : Nat) (reachable : List String) : List String :=
    match fuel with
    | 0 => reachable
    | fuel + 1 =>
        let expanded :=
          reachable.foldl (fun acc name =>
            match libraries.find? (fun fn => fn.name = name) with
            | some fn =>
                let deps := (callNamesInLibraryBody fn.body).filter
                  (fun dep => providedFunctions.contains dep)
                (acc ++ deps).eraseDups
            | none => acc) reachable
        if expanded.length = reachable.length then
          reachable
        else
          expand fuel expanded
  expand (libraries.length + 1) seed

def selectDirectlyReferencedLibraries (obj : YulObject) (libraries : List LibraryFunction) : List LibraryFunction :=
  let referenced := collectExternalCallNames obj libraries
  let referencedClosure := collectReferencedLibraryClosure libraries referenced
  libraries.filter fun fn => referencedClosure.contains fn.name

/-- Smoke test: referenced-library selection keeps transitive helper dependencies. -/
example :
    let obj : YulObject :=
      { name := "Main"
        deployCode := []
        runtimeCode := [.exprStmt (.call "A" [])] }
    let libs : List LibraryFunction :=
      [ { name := "A", arity := 0, body := ["function A() {", "B()", "}"] }
      , { name := "B", arity := 0, body := ["function B() {", "let x := 1", "}"] }
      , { name := "C", arity := 0, body := ["function C() {", "let y := 2", "}"] }
      ]
    (selectDirectlyReferencedLibraries obj libs).map (·.name) = ["A", "B"] := by
  native_decide

-- Validate that all external calls are provided by libraries
-- Excludes Yul builtins and locally-defined functions
def validateExternalReferences (obj : YulObject) (libraries : List LibraryFunction) : Except String Unit := do
  let (allCalls, localDefs, providedFunctions) := externalReferenceContext obj libraries
  let missingFunctions := allCalls.filter fun call =>
    !isYulBuiltinCall call && !localDefs.contains call && !providedFunctions.contains call
  if !missingFunctions.isEmpty then
    throw s!"Unresolved external references: {String.intercalate ", " missingFunctions}"
  pure ()

-- Validate that library function call sites match library parameter counts.
-- Catches bugs where a library exports a different arity than the contract expects.
def validateCallArity (obj : YulObject) (libraries : List LibraryFunction) : Except String Unit := do
  let allCode := obj.deployCode ++ obj.runtimeCode
  let callsWithArity := callsWithArityFromStmts allCode
  let libArityMap := libraries.map fun lib => (lib.name, lib.arity)
  let mut errors : List String := []
  for (callName, callArity) in callsWithArity do
    match libArityMap.lookup callName with
    | some libArity =>
      if callArity != libArity then
        errors := s!"{callName}: called with {callArity} args but library defines {libArity} params" :: errors
    | none => pure ()  -- Not a library function; skip
  if !errors.isEmpty then
    throw s!"Arity mismatch: {String.intercalate "; " errors.eraseDups}"
  pure ()

end Compiler.Linker
