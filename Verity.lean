-- Verity Framework — compiler-free umbrella for the standalone EDSL package.
-- Compiler-backed macros/lowering live in `verity-compiler` until #1313 moves
-- the shared compilation-model types into the EDSL layer.
import Verity.Core
import Verity.Core.Int256
import Verity.Core.Semantics
import Verity.Core.Uint256
import Verity.Core.FiniteSet
import Verity.Core.Free.TypedIR
import Verity.Core.Free.ContractStep
import Verity.Core.Model.DenoteExternalCode
import Verity.Core.Model.DenoteLowLevelCall
import Verity.Core.Model.DenoteStaticCall
import Verity.Core.Model.DenoteExternalCodeCopy
import Verity.EVM.Int256
import Verity.EVM.Uint256
import Verity.Stdlib.Math
import Verity.Specs.Common
import Verity.Specs.Common.Sum
import Verity.Specs.Composition
import Verity.Proofs.Stdlib.Math
import Verity.Proofs.Stdlib.ListSum
import Verity.Core.SafeArith
import Verity.Core.BoundedLoops
import Verity.Macro.Types
import Verity.Macro.SpecGen
import Verity.Proofs.Stdlib.Automation
