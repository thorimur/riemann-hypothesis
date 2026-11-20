import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnramifiedQuadraticConditionFive
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unramified_quadratic_condition_five : PositivityTheory.SiegelWeilFormula.Gunr.Q5 := by
  first | exact @GlobalTheory.CompanionTheory.GunrInert.isField_tensor_iff_isField_quot | exact GlobalTheory.CompanionTheory.GunrInert.isField_tensor_iff_isField_quot | (intros; apply GlobalTheory.CompanionTheory.GunrInert.isField_tensor_iff_isField_quot <;> assumption)
