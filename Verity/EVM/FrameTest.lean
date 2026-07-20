import Verity.EVM.Frame

namespace Verity.EVM.FrameTest

open Verity.EVM.Frame

/-- Regression: the type of every returndata lookup carries its payload bound. -/
example (data : ReturnData) (idx : Nat) (hIdx : idx < data.size) :
    data.lookup ⟨idx, hIdx⟩ = data.wordAt ⟨idx, hIdx⟩ :=
  ReturnData.lookup_eq_wordAt data ⟨idx, hIdx⟩

/-- The frame-level API retains the same bounds at the caller boundary. -/
example (caller : CallerFrame) (idx : Nat) (hIdx : idx < returndataSize caller) :
    returndataWord caller ⟨idx, hIdx⟩ = caller.returnDataBuf.wordAt ⟨idx, hIdx⟩ := rfl

end Verity.EVM.FrameTest
