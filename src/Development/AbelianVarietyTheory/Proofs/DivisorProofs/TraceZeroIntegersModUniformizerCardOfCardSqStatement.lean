import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TraceZeroIntegersModUniformizerCardOfCardSq
open Formalism.UG GlobalTheory.SatakeWeyl
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.traceZeroIntegersModUniformizerCard_of_cardSq : GlobalTheory.SatakeWeyl.IntIndex → GlobalTheory.SatakeWeyl.TraceZeroIndex := by
  first | exact @GlobalTheory.SatakeWeyl.traceZeroIndex_of_intIndex | exact GlobalTheory.SatakeWeyl.traceZeroIndex_of_intIndex | (intros; apply GlobalTheory.SatakeWeyl.traceZeroIndex_of_intIndex <;> assumption)
