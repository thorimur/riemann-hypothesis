import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GaussianSchwartzBruhat
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.gaussian_schwartz_bruhat : Ad3.R.GS := by
  first | exact @GlobalTheory.CompanionTheory.RankinSelberg.gaussian_exists | exact GlobalTheory.CompanionTheory.RankinSelberg.gaussian_exists | (intros; apply GlobalTheory.CompanionTheory.RankinSelberg.gaussian_exists <;> assumption)
