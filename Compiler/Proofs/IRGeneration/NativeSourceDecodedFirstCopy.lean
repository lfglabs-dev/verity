import Compiler.Proofs.IRGeneration.NativeSourcePreludeDecoded

namespace Compiler.Proofs.IRGeneration.NativeSourceDecodedFirstCopy
open EvmYul EVM.Proof NativeSourcePreludeDecoded

theorem run4 (fuel cost : Nat) (pre : EVM.State)
    (length a b c d e f g dest : UInt256) (tail : Stack UInt256)
    (code : pre.executionEnv.code = NativeSourceAbiWrite.code) (pc : pre.pc = UInt256.ofNat 644)
    (stack : pre.stack = length :: a :: b :: c :: d :: e :: f :: g :: dest :: tail) :
    run fuel cost 4 pre =
      .ok (NativeSourceFirstCopy.copied pre cost cost cost cost length a b c d e f g dest tail) := by
  have executed := NativeSourceFirstCopy.execute fuel cost cost cost cost pre length a b c d e f g dest tail code pc stack
  have finish (step : Except EVM.ExecutionException EVM.State) : (step >>= Except.ok) = step := by
    cases step <;> rfl
  simp only [bind_assoc] at executed
  simpa only [run, finish, bind_assoc] using executed

theorem execute (fuel cost : Nat) (pre : EVM.State) (free a b c d e f g h : UInt256)
    (tail : Stack UInt256) (code : pre.executionEnv.code = NativeSourceAbiWrite.code)
    (pc : pre.pc = UInt256.ofNat 636)
    (stack : pre.stack = free :: a :: b :: c :: d :: e :: f :: g :: h :: tail) :
    run fuel cost 12 pre =
      .ok (NativeSourcePreludeCopy.copied cost cost cost cost cost cost pre free a b c d e f g h tail) := by
  rw [show 12 = 8 + 4 by decide, run_add, execute8 fuel cost pre free a b c d e f g h tail code pc stack]
  simp only [Bind.bind, Except.bind]
  exact run4 fuel cost _ (NativeSourcePreludeCopy.length cost pre free a b c d e f g h tail)
    c e a b free d free (free + b) (g :: h :: tail) code
    (NativeSourcePreludeCopy.entry_pc cost cost pre free a b c d e f g h tail pc)
    (NativeSourcePreludeLength.stack cost cost pre free a b c d e f g h tail)

end Compiler.Proofs.IRGeneration.NativeSourceDecodedFirstCopy
