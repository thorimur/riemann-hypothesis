import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArithmeticRiemannRochAbelianQuoted
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.arithmetic_riemann_roch_abelian_quoted : GlobalTheory.CovTop.Hypotheses2 → GlobalTheory.Published.RegularAlteration → GlobalTheory.Published.ArithRiemannRoch → GlobalTheory.Published.ArithRiemannRochAbelian := by
  first | exact @GlobalTheory.arithRiemannRochAbelian_of_knownResults_known | exact GlobalTheory.arithRiemannRochAbelian_of_knownResults_known | (intros; apply GlobalTheory.arithRiemannRochAbelian_of_knownResults_known <;> assumption)
