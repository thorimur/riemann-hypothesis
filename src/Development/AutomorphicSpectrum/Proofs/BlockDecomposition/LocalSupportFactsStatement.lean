import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalSupportFacts
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_support_facts : PositivityTheory.Rg.BcB.G8.Fin.LocSupp := by
  first | exact @GlobalTheory.CompanionTheory.TwistOrbit.locSupp | exact GlobalTheory.CompanionTheory.TwistOrbit.locSupp | (intros; apply GlobalTheory.CompanionTheory.TwistOrbit.locSupp <;> assumption)
