import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogNormIntegrablePoincare
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.log_norm_integrable_poincare : GlobalTheory.Published.AnalyticLogResolution → GlobalTheory.Published.AnalyticSetDimension → GlobalTheory.IndefiniteRowSideFullHecke.BoundaryPolynomialFunctions.LogNormIntegrablePoincare := by
  first | exact @GlobalTheory.LogResInt.logNormIntegrablePoincare | exact GlobalTheory.LogResInt.logNormIntegrablePoincare | (intros; apply GlobalTheory.LogResInt.logNormIntegrablePoincare <;> assumption)
