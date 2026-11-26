import Contracts.SolidityImportSmoke.LowLevelStaticcallSequenceModel

namespace SolidityImportSmoke.LowLevelStaticcallChecks

-- Low-level `staticcall` (#2948) is a closed static call (`YulMemoryCall.module true`), never
-- opening a reentrancy window (`reentrancyTrusted = false`, `reentrancyAdversarial = false`),
-- while allowing post-call storage writes under `solidity_static_call_cei` (#2940 / #2911).
#guard match LowLevelStaticcallSequenceModel.model.functions.find? (·.name == "record") with
  | some fn =>
      fn.allowPostInteractionWrites && !fn.reentrancyTrusted && !fn.reentrancyAdversarial &&
        fn.localObligations.any (·.name == "solidity_static_call_cei") &&
        !fn.localObligations.any (·.name == "solidity_post_call_state_access")
  | none => false

#guard match LowLevelStaticcallSequenceModel.model.functions.find? (·.name == "isValid") with
  | some fn =>
      !fn.allowPostInteractionWrites && !fn.reentrancyTrusted && !fn.reentrancyAdversarial &&
        !fn.localObligations.any (·.name == "solidity_post_call_state_access")
  | none => false

#guard match LowLevelStaticcallSequenceModel.model.functions.find? (·.name == "checkBytes") with
  | some fn =>
      !fn.allowPostInteractionWrites && !fn.reentrancyTrusted && !fn.reentrancyAdversarial &&
        !fn.localObligations.any (·.name == "solidity_post_call_state_access")
  | none => false

end SolidityImportSmoke.LowLevelStaticcallChecks
