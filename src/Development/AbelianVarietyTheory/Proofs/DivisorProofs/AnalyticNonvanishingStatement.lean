import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AnalyticNonvanishing
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.analytic_nonvanishing : GlobalTheory.ThK.KP → GlobalTheory.ThK.NonZeroAn := by
  first | exact @GlobalTheory.ThKNonZero.nonZeroAn | exact GlobalTheory.ThKNonZero.nonZeroAn | (intros; apply GlobalTheory.ThKNonZero.nonZeroAn <;> assumption)
