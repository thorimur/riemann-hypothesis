import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EisensteinBasicFirst
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eisenstein_basic_first : Ad3.R.B0 → Ad3.R.E1 := by
  first | exact @GlobalTheory.CompanionTheory.RSEuler.eulerProduct_integral | exact GlobalTheory.CompanionTheory.RSEuler.eulerProduct_integral | (intros; apply GlobalTheory.CompanionTheory.RSEuler.eulerProduct_integral <;> assumption)
