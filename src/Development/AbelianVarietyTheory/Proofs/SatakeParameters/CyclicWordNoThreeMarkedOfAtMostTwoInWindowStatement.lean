import Development.AbelianVarietyTheory.Proofs.SatakeParameters.CyclicWordNoThreeMarkedOfAtMostTwoInWindow
open GlobalTheory.HTW Formalism.BasicNotions Formalism.FrobeniusOrbits
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cyclicWord_noThreeMarked_of_atMostTwoInWindow : ∀ {n : ℕ} (th : ZMod n → Prop) (L : ℕ), 3 ≤ L → WindowTwo th L → NoThree th ∧ ∃ i, ¬ th i := by
  first | exact @GlobalTheory.noThree_of_windowTwo | exact GlobalTheory.noThree_of_windowTwo | (intros; apply GlobalTheory.noThree_of_windowTwo <;> assumption)
