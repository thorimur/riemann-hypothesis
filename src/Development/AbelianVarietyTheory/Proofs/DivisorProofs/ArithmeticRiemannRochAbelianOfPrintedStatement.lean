import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArithmeticRiemannRochAbelianOfQuoted
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.arithmetic_riemann_roch_abelian_of_quoted : GlobalTheory.CovTop.Hypotheses2 → GlobalTheory.Published.RegularAlteration → GlobalTheory.Published.ArithRiemannRoch → GlobalTheory.Published.ArithRiemannRochAbelian := by
  first | exact @GlobalTheory.AbelianRR.main | exact GlobalTheory.AbelianRR.main | (intros; apply GlobalTheory.AbelianRR.main <;> assumption)
