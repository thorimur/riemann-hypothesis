import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.InvIsoOfLocalTateDuality

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.invIso_of_localTateDuality : Formalism.GaloisCohomology.LocalTateDualityK → ReciprocityTheory.ChartRestriction.T2.InvIso := by
  first | exact @GlobalTheory.InvColim.inv_iso | exact GlobalTheory.InvColim.inv_iso | (intros; apply GlobalTheory.InvColim.inv_iso <;> assumption)
