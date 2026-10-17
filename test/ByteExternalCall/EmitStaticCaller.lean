import Compiler.Modules.SolidityStaticCall
import Compiler.Yul.PrettyPrint

open Compiler.Yul

def main (args : List String) : IO UInt32 := do
  let [output] := args | throw (IO.userError "expected OUTPUT")
  -- price() selector. This is a transport fixture, not an imported contract.
  let statements ← IO.ofExcept
    ((Compiler.Modules.SolidityStaticCall.uint256Module "result" 0xa035b1fe 0).compileCanonical
      {} [.call "calldataload" [.lit 4]])
  let body := [.exprStmt (.call "mstore" [.lit 64, .lit 128])] ++ statements ++
    [.exprStmt (.call "mstore" [.lit 0, .ident "result"]),
     .exprStmt (.call "return" [.lit 0, .lit 32])]
  let runtime := String.intercalate "\n" (ppStmts 0 body)
  IO.FS.writeFile output
    ("object \"Caller\" { code { datacopy(0, dataoffset(\"Runtime\"), datasize(\"Runtime\")) " ++
     "return(0, datasize(\"Runtime\")) } object \"Runtime\" { code {\n" ++ runtime ++ "\n} } }")
  return 0
