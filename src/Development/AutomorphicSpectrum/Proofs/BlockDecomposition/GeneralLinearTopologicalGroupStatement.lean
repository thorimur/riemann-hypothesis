import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GeneralLinearTopologicalGroup
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.general_linear_topological_group : PositivityTheory.RgEis.GrpTop := by
  first | exact @GlobalTheory.CompanionTheory.RgEisTop.grpTop | exact GlobalTheory.CompanionTheory.RgEisTop.grpTop | (intros; apply GlobalTheory.CompanionTheory.RgEisTop.grpTop <;> assumption)
