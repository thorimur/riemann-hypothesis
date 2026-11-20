import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ChoiceOfTops
import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.EvalFrameOrd
open GlobalTheory.NT Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory Formalism.BasicNotions NumberField IsDedekindDomain
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.choice_of_tops : Formalism.G0.TileConditionFailureProbBound := by
  first | exact @GlobalTheory.RandomTops.prob_not_good_le | exact GlobalTheory.RandomTops.prob_not_good_le | (intros; apply GlobalTheory.RandomTops.prob_not_good_le <;> assumption)
