import Verity.Core.Model.Denote

/-! Bounded structural frame proof for the physical ABI scratch stores.
This proof uses induction over argument expressions, never reduces a whole
compiled contract, and assumes only successful expression evaluation. -/
namespace Compiler.CompilationModel.Denote

/-- The scratch-store sequence cannot change any account-qualified storage
slot. The argument observer records exactly the same successful sequence. -/
theorem byteStaticArgumentStores_storage_frame
    (oracle : DenoteOracle) (fields : List Field) (pointer : Nat)
    (before after : DenoteState) (index : Nat) (args : List Expr)
    (reads : List (DenoteState × Expr))
    (executed : byteStaticArgumentStores oracle fields pointer before index args =
      some (after, reads)) :
    after.world.storageWords = before.world.storageWords := by
  induction args generalizing before after index reads with
  | nil =>
      simp only [byteStaticArgumentStores, Option.some.injEq] at executed
      cases executed
      rfl
  | cons argument rest ih =>
      cases evaluated : evalExpr oracle fields before argument with
      | none => simp [byteStaticArgumentStores, evaluated] at executed
      | some value =>
          let world := before.world.writePhysicalMemoryValue
            (wordNormalize (pointer + 4 + index * 32)) (Verity.Core.Uint256.ofNat value)
          let next := { before with world }
          have step :
              byteStaticArgumentStores oracle fields pointer before index (argument :: rest) =
              (byteStaticArgumentStores oracle fields pointer next (index + 1) rest).map
                (fun (final, observed) => (final, (before, argument) :: observed)) := by
            simp only [byteStaticArgumentStores, evaluated]
            change (byteStaticArgumentStores oracle fields pointer next (index + 1) rest).bind _ = _
            cases byteStaticArgumentStores oracle fields pointer next (index + 1) rest <;> rfl
          rw [step] at executed
          cases tail : byteStaticArgumentStores oracle fields pointer next (index + 1) rest with
          | none => simp [tail] at executed
          | some result =>
              rcases result with ⟨final, observed⟩
              simp only [tail, Option.map_some, Option.some.injEq] at executed
              have same : final = after := congrArg Prod.fst executed
              subst after
              exact ih next final (index + 1) observed tail

end Compiler.CompilationModel.Denote
