import Compiler.Proofs.IRGeneration.HelperSummaryEvidence
import Compiler.Proofs.HelperStepProofs

namespace Compiler.Proofs.IRGeneration.Regression

open Compiler
open Compiler.CompilationModel
open Compiler.Proofs.HelperStepProofs

/-- Concrete `helperA → helperB` void-call catalog witness.  The supplied
call-site evidence is deliberately the final body-correspondence seam: its
`sufficient` component contains the `InternalHelperBodyExecContext`, while the
producer itself obtains the callee through the runtime table, uses the
selector-aware exact summary, and passes the strict rank decrease to `hsite`.
Consequently mutations that remove lookup, void-call execution, selector/world
projection, body context, or rank evidence make this witness ill-typed. -/
theorem helperA_helperB_voidCall_catalogWithInternals_of_bodyEvidence
    {runtimeContract : IRContract}
    (hRuntime : SupportedRuntimeHelperTableInterface twoHelperSpec runtimeContract)
    (hsite :
      ∀ {scope calleeName args}
        (hoccurs : StmtOccursAtScope [] scope
          (Stmt.internalCall calleeName args) helperA.body)
        (hmem : calleeName ∈ helperCallNames helperA),
        (helperA_supportedBodyHelperInterface.summaryOfCall hmem).summary.helperRank <
            helperA_supportedBodyHelperInterface.helperRank →
        DirectInternalHelperCallSiteEvidence runtimeContract twoHelperSpec [] scope
          calleeName args
          (directInternalHelperStatementContextBridge_of_supportedEvidence
            helperA_supportedBodyHelperInterface
            (fun selector calleeName hmem => by
              have hname : calleeName = "helperB" := by
                simpa [helperA, helperCallNames, stmtListInternalHelperCallNames,
                  stmtInternalHelperCallNames, exprInternalHelperCallNames,
                  exprListInternalHelperCallNames] using hmem
              subst calleeName
              exact helperB_exactSummary_soundAtSelector selector)
            hRuntime hmem)) :
    DirectInternalHelperCallHeadStepCatalogWithInternals
      runtimeContract twoHelperSpec [] [] helperA := by
  apply directInternalHelperCallHeadStepCatalogWithInternals_of_supportedEvidence
    helperA_supportedBodyHelperInterface (by decide)
    helperA_supportedBodyHelperInterface_summary_sound
    (fun selector calleeName hmem => ?_) hRuntime hsite
  have hname : calleeName = "helperB" := by
    simpa [helperA, helperCallNames, stmtListInternalHelperCallNames,
      stmtInternalHelperCallNames, exprInternalHelperCallNames,
      exprListInternalHelperCallNames] using hmem
  subst calleeName
  exact helperB_exactSummary_soundAtSelector selector

end Compiler.Proofs.IRGeneration.Regression
