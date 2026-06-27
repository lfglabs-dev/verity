/-
  Correctness and read-only proofs for Counter's view/preview functions.

  `previewAddTwice` and `previewOps` are pure view functions that read storage
  but never write it. These proofs establish their functional results and that
  they leave the contract state untouched. They previously had no proofs.
-/

import Contracts.Counter.Spec
import Verity.Proofs.Stdlib.Automation

namespace Contracts.Counter.Proofs

open Verity
open Contracts.Counter
open Verity.EVM.Uint256

/-! ## previewAddTwice -/

theorem previewAddTwice_correct (s : ContractState) (delta : Uint256) :
    let result := ((previewAddTwice delta).run s).fst
    result = EVM.Uint256.add (EVM.Uint256.add (s.storage 0) delta) delta := by
  simp [previewAddTwice, count, getStorage, Contract.run, ContractResult.fst,
    Verity.bind, Bind.bind, Verity.pure, Pure.pure]

theorem previewAddTwice_preserves_state (s : ContractState) (delta : Uint256) :
    let s' := ((previewAddTwice delta).run s).snd
    s' = s := by
  simp [previewAddTwice, count, getStorage, Contract.run, ContractResult.snd,
    Verity.bind, Bind.bind, Verity.pure, Pure.pure]

/-! ## previewOps -/

theorem previewOps_preserves_state (s : ContractState) (x y z : Uint256) :
    let s' := ((previewOps x y z).run s).snd
    s' = s := by
  simp [previewOps, Contract.run, ContractResult.snd, Verity.pure, Pure.pure]

end Contracts.Counter.Proofs
