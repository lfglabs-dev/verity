import Compiler.Proofs.LoopSimulation

/-! Public compatibility import for the Phase 1K loop-simulation library. -/

namespace Verity.Proofs.LoopSimulation

export Compiler.Proofs.LoopSimulation
  (EnvAccRel IndexInvariant UInt256 foldl_eq_forEach foldl_rel forEach
    forEach_eq_foldl forEach_preserves_indexInvariant forEach_rel
    forEach_sum_over_array forEach_trace_order forEachFrom
    forEachFrom_eq_foldl forEachFrom_preserves_indexInvariant
    iterateMappingWrites iterateMappingWrites_eq_stateRewrite loopIndices
    mappingIteration_compiled_eq_canonical mappingReadAt_of_key mappingWrite
    normalizeUInt256 normalizeUInt256_add normalizeUInt256_eq_self
    normalizeUInt256_eq_val normalizeUInt256_idem normalizeUInt256_lt
    normalizeUInt256_succ sumStep traceStep)

end Verity.Proofs.LoopSimulation
