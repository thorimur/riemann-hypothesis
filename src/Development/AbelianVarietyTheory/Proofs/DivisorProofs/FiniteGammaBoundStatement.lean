import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteGammaBound
open GlobalTheory.SumSize GlobalTheory.RowClaim
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_gamma_bound : GlobalTheory.FunPr.Hypotheses₂ → FinGamK := by
  first | exact @GlobalTheory.GamLoss.finGamK | exact GlobalTheory.GamLoss.finGamK | (intros; apply GlobalTheory.GamLoss.finGamK <;> assumption)
