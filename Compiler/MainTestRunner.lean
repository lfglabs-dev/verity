import Compiler.MainTest

unsafe def main (args : List String) : IO UInt32 := do
  match args with
  | [] =>
    -- Local convenience: whole suite in one process. CI runs one phase per
    -- process instead so interpreter memory resets between phases (#2214).
    Compiler.MainTest.runTests
    pure 0
  | [phase] => Compiler.MainTest.runPhase phase
  | _ =>
    IO.eprintln "usage: compiler-main-test [flags|compile|gates|mechanics]"
    pure 2
