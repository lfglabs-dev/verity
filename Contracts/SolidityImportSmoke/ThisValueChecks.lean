import Contracts.SolidityImportSmoke.ThisValueSequenceModel

namespace SolidityImportSmoke.ThisValueChecks

/-- `domainSeparator` (`this`) and `domainSeparatorAddress` (`address(this)`) lower to the
exact same `CompilationModel` body. -/
theorem domainSeparator_body_eq :
    (ThisValueSequenceModel.model.functions.find? (·.name == "domainSeparator")).map (·.body) =
      (ThisValueSequenceModel.model.functions.find?
        (·.name == "domainSeparatorAddress")).map (·.body) := rfl

end SolidityImportSmoke.ThisValueChecks
