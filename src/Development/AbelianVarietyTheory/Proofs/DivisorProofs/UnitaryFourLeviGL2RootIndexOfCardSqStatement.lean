import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryFourLeviGL2RootIndexOfCardSq
open Formalism.UG GlobalTheory.SatakeWeyl
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitaryFourLeviGL2RootIndex_of_cardSq : GlobalTheory.SatakeWeyl.IntIndex → GlobalTheory.SatakeWeyl.IndexFour := by
  first | exact @GlobalTheory.SatakeWeyl.IdxFour.indexFour | exact GlobalTheory.SatakeWeyl.IdxFour.indexFour | (intros; apply GlobalTheory.SatakeWeyl.IdxFour.indexFour <;> assumption)
