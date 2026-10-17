import Contracts.SolidityImportSmoke.NativeMidnightCollisionChecks
import Contracts.SolidityImportSmoke.NativeMidnightInvalidChecks

def main : IO Unit := do
  MidnightSourceCaller.runFailures false
  MidnightSourceCaller.runInvalid false
