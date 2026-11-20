import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DecompositionGroupEquivLocalGaloisGroup

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.decomposition_group_equiv_local_galois_group : ReciprocityTheory.ChartRestriction.T2.DecEquiv := by
  first | exact @GlobalTheory.DecLocal.decEquiv | exact GlobalTheory.DecLocal.decEquiv | (intros; apply GlobalTheory.DecLocal.decEquiv <;> assumption)
