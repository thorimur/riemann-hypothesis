import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SplitExEveryDatum
open Formalism.BasicNotions NumberField IsDedekindDomain
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.splitEx_every_datum : ∀ D : D7, Formalism.L2.SplitEx D := by
  first | exact @GlobalTheory.SplitConjPlace.splitEx_all | exact GlobalTheory.SplitConjPlace.splitEx_all | (intros; apply GlobalTheory.SplitConjPlace.splitEx_all <;> assumption)
