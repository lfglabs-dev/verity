import Compiler.Proofs.IRGeneration.NativeSourceAbiInputs

namespace Compiler.Proofs.IRGeneration.NativeSourceMarketCalldata
open EvmYul Compiler.Proofs.YulGeneration.Backends

structure Collateral where
  token : Nat
  lltv : Nat
  liquidationCursor : Nat
  oracle : Nat

def Collateral.words (c : Collateral) : List Nat :=
  [c.token, c.lltv, c.liquidationCursor, c.oracle]

structure Market where
  chainId : Nat
  midnight : Nat
  loanToken : Nat
  maturity : Nat
  rcfThreshold : Nat
  enterGate : Nat
  liquidatorGate : Nat
  collateral : List Collateral

/-- ABI arguments of SourceCaller.deploy; offsets exclude the four-byte selector. -/
def arguments (m : Market) (key value : Nat) : List Nat :=
  [96, key, value, m.chainId, m.midnight, m.loanToken, 256, m.maturity,
    m.rcfThreshold, m.enterGate, m.liquidatorGate, m.collateral.length] ++
      m.collateral.flatMap Collateral.words

theorem collateral_length (cs : List Collateral) :
    (cs.flatMap Collateral.words).length = 4 * cs.length := by
  induction cs with
  | nil => rfl
  | cons c cs ih => simp only [List.flatMap_cons, List.length_append, Collateral.words,
      List.length_cons, List.length_nil, ih]; omega

theorem collateral_drop (prior suffix : List Collateral) (c : Collateral) :
    ((prior ++ c :: suffix).flatMap Collateral.words).drop (4 * prior.length) =
      c.words ++ suffix.flatMap Collateral.words := by
  rw [List.flatMap_append, ← collateral_length prior]
  simp only [List.drop_left, List.flatMap_cons]

theorem header (machine : EVM.State) (selector key value : Nat) (m : Market)
    (encoded : machine.executionEnv.calldata = StateBridge.calldataToByteArray selector (arguments m key value)) :
    (machine.toState.calldataload (UInt256.ofNat 100)).toNat = m.chainId % Compiler.Constants.evmModulus ∧
    (machine.toState.calldataload (UInt256.ofNat 132)).toNat = m.midnight % Compiler.Constants.evmModulus ∧
    (machine.toState.calldataload (UInt256.ofNat 164)).toNat = m.loanToken % Compiler.Constants.evmModulus ∧
    (machine.toState.calldataload (UInt256.ofNat 196)).toNat = 256 % Compiler.Constants.evmModulus ∧
    (machine.toState.calldataload (UInt256.ofNat 228)).toNat = m.maturity % Compiler.Constants.evmModulus ∧
    (machine.toState.calldataload (UInt256.ofNat 260)).toNat = m.rcfThreshold % Compiler.Constants.evmModulus ∧
    (machine.toState.calldataload (UInt256.ofNat 292)).toNat = m.enterGate % Compiler.Constants.evmModulus ∧
    (machine.toState.calldataload (UInt256.ofNat 324)).toNat = m.liquidatorGate % Compiler.Constants.evmModulus ∧
    (machine.toState.calldataload (UInt256.ofNat 356)).toNat = m.collateral.length % Compiler.Constants.evmModulus := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact NativeSourceAbiInputs.encoded_argument machine selector _ 3 _ _ encoded rfl (by decide)
  · exact NativeSourceAbiInputs.encoded_argument machine selector _ 4 _ _ encoded rfl (by decide)
  · exact NativeSourceAbiInputs.encoded_argument machine selector _ 5 _ _ encoded rfl (by decide)
  · exact NativeSourceAbiInputs.encoded_argument machine selector _ 6 _ _ encoded rfl (by decide)
  · exact NativeSourceAbiInputs.encoded_argument machine selector _ 7 _ _ encoded rfl (by decide)
  · exact NativeSourceAbiInputs.encoded_argument machine selector _ 8 _ _ encoded rfl (by decide)
  · exact NativeSourceAbiInputs.encoded_argument machine selector _ 9 _ _ encoded rfl (by decide)
  · exact NativeSourceAbiInputs.encoded_argument machine selector _ 10 _ _ encoded rfl (by decide)
  · exact NativeSourceAbiInputs.encoded_argument machine selector _ 11 _ _ encoded rfl (by decide)

theorem element (machine : EVM.State) (selector key value : Nat) (m : Market)
    (prior suffix : List Collateral) (c : Collateral)
    (decomposed : m.collateral = prior ++ c :: suffix)
    (encoded : machine.executionEnv.calldata = StateBridge.calldataToByteArray selector (arguments m key value))
    (bounded : 4 + 32 * (15 + 4 * prior.length) < 2 ^ 64) :
    (machine.toState.calldataload (UInt256.ofNat (4 + 32 * (12 + 4 * prior.length)))).toNat = c.token % Compiler.Constants.evmModulus ∧
    (machine.toState.calldataload (UInt256.ofNat (4 + 32 * (13 + 4 * prior.length)))).toNat = c.lltv % Compiler.Constants.evmModulus ∧
    (machine.toState.calldataload (UInt256.ofNat (4 + 32 * (14 + 4 * prior.length)))).toNat = c.liquidationCursor % Compiler.Constants.evmModulus ∧
    (machine.toState.calldataload (UInt256.ofNat (4 + 32 * (15 + 4 * prior.length)))).toNat = c.oracle % Compiler.Constants.evmModulus := by
  have dropped : (arguments m key value).drop (12 + 4 * prior.length) =
      c.words ++ suffix.flatMap Collateral.words := by
    unfold arguments
    rw [List.drop_append]
    simp only [List.length_cons, List.length_nil]
    rw [show 12 + 4 * prior.length - 12 = 4 * prior.length by omega, decomposed, collateral_drop]
    simp
  refine ⟨?_, ?_, ?_, ?_⟩
  · apply NativeSourceAbiInputs.encoded_argument machine selector _ (12 + 4 * prior.length) c.token ([c.lltv, c.liquidationCursor, c.oracle] ++ suffix.flatMap Collateral.words) encoded
    · have rest := congrArg (List.drop 0) dropped
      rw [List.drop_drop, show (12 + 4 * prior.length) + 0 = 12 + 4 * prior.length by omega] at rest
      simpa [Collateral.words] using rest
    · omega
  · apply NativeSourceAbiInputs.encoded_argument machine selector _ (13 + 4 * prior.length) c.lltv ([c.liquidationCursor, c.oracle] ++ suffix.flatMap Collateral.words) encoded
    · have rest := congrArg (List.drop 1) dropped
      rw [List.drop_drop, show (12 + 4 * prior.length) + 1 = 13 + 4 * prior.length by omega] at rest
      simpa [Collateral.words] using rest
    · omega
  · apply NativeSourceAbiInputs.encoded_argument machine selector _ (14 + 4 * prior.length) c.liquidationCursor ([c.oracle] ++ suffix.flatMap Collateral.words) encoded
    · have rest := congrArg (List.drop 2) dropped
      rw [List.drop_drop, show (12 + 4 * prior.length) + 2 = 14 + 4 * prior.length by omega] at rest
      simpa [Collateral.words] using rest
    · omega
  · apply NativeSourceAbiInputs.encoded_argument machine selector _ (15 + 4 * prior.length) c.oracle ([] ++ suffix.flatMap Collateral.words) encoded
    · have rest := congrArg (List.drop 3) dropped
      rw [List.drop_drop, show (12 + 4 * prior.length) + 3 = 15 + 4 * prior.length by omega] at rest
      simpa [Collateral.words] using rest
    · omega

end Compiler.Proofs.IRGeneration.NativeSourceMarketCalldata
