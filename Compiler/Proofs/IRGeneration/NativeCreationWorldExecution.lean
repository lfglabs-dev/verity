import Compiler.Proofs.IRGeneration.NativeCreationWorldCaller

/-! Execute the paired world-changing prefix before the existing creation
operation. Native account resynchronization remains a separate obligation. -/
namespace Compiler.Proofs.IRGeneration.NativeCreationWorldExecution
open NativeCreationWorldCaller

/-- No stale entry world is substituted for the actual paired prefix world. -/
def run (fuel : Nat) (before : Frame) : Except String CreationBytecode.Outcome := do
  match ← NativeCreationWorldCaller.run fuel before with
  | .exceptional _ frame => pure (.exceptional frame)
  | .ready frame => CreationBytecode.execReady frame

/-- Reaching CREATE2 delegates with precisely the executed prefix frame. -/
theorem run_ready (fuel : Nat) (before boundary : Frame)
    (ready : NativeCreationWorldCaller.run fuel before = .ok (.ready boundary)) :
    run fuel before = CreationBytecode.execReady boundary := by
  simp [run, ready, Bind.bind, Except.bind]

end Compiler.Proofs.IRGeneration.NativeCreationWorldExecution
