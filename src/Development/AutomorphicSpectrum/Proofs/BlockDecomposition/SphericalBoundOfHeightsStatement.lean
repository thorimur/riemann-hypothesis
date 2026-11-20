import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SphericalBoundOfHeights
open PositivityTheory.Rg.Rsw
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.spherical_bound_of_heights : HtExist → SphBound := by
  first | exact @GlobalTheory.CompanionTheory.SphPole.sphBound_of_htExist | exact GlobalTheory.CompanionTheory.SphPole.sphBound_of_htExist | (intros; apply GlobalTheory.CompanionTheory.SphPole.sphBound_of_htExist <;> assumption)
