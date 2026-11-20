import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryRankThreeRootIndexOfCards
open Formalism.UG GlobalTheory.SatakeWeyl
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitaryRankThreeRootIndex_of_cards : GlobalTheory.SatakeWeyl.IntIndex → GlobalTheory.SatakeWeyl.TraceZeroIndex → GlobalTheory.SatakeWeyl.IndexThree := by
  first | exact @GlobalTheory.SatakeWeyl.Heis.indexThree | exact GlobalTheory.SatakeWeyl.Heis.indexThree | (intros; apply GlobalTheory.SatakeWeyl.Heis.indexThree <;> assumption)
