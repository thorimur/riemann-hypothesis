import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LValueRatioLowerBoundGauge
open GlobalTheory.SqTop
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lValueRatio_lower_bound_gauge : GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds.ToricDenominator → FieldDat → TorEx → RhoLow := by
  first | exact @GlobalTheory.RhoLowProof.rhoLow_holds | exact GlobalTheory.RhoLowProof.rhoLow_holds | (intros; apply GlobalTheory.RhoLowProof.rhoLow_holds <;> assumption)
