namespace Compiler

/-- ASCII letter check used for Solidity-style identifiers. -/
def isAsciiLetter (c : Char) : Bool :=
  ('a' ≤ c && c ≤ 'z') || ('A' ≤ c && c ≤ 'Z')

/-- ASCII digit check used for Solidity-style identifiers. -/
def isAsciiDigit (c : Char) : Bool :=
  '0' ≤ c && c ≤ '9'

/-- Identifier start character: ASCII letter or underscore. -/
def isIdentifierStart (c : Char) : Bool :=
  isAsciiLetter c || c = '_'

/-- Identifier continuation character: start chars plus ASCII digits. -/
def isIdentifierContinue (c : Char) : Bool :=
  isIdentifierStart c || isAsciiDigit c

/-- Shared identifier validator for AST and CompilationModel frontends. -/
def isValidIdentifier (name : String) : Bool :=
  match name.data with
  | [] => false
  | c :: cs => isIdentifierStart c && cs.all isIdentifierContinue

/-- Shared diagnostic helper for frontend identifier validation. -/
def ensureValidIdentifier (kind name : String) : Except String Unit := do
  if !isValidIdentifier name then
    throw s!"{kind} name must be a valid identifier: {name}"

end Compiler
