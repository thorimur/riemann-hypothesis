import Development.AbelianVarietyTheory.Proofs.TwistedOperators.TraceZeroIntegersIndexInUniformizerMultiples
open GlobalTheory.InertZeta
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.traceZero_integers_index_in_uniformizer_multiples : TraceIndex := by
  first | exact @GlobalTheory.InertZeta.traceIndex | exact GlobalTheory.InertZeta.traceIndex | (intros; apply GlobalTheory.InertZeta.traceIndex <;> assumption)
