import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MultiplicativityFinitePlaces
open Matrix PositivityTheory.Rg.BcB.D1
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.multiplicativity_finite_places : MulF := by
  first | exact @GlobalTheory.CompanionTheory.WedgeMinor.mulF | exact GlobalTheory.CompanionTheory.WedgeMinor.mulF | (intros; apply GlobalTheory.CompanionTheory.WedgeMinor.mulF <;> assumption)
