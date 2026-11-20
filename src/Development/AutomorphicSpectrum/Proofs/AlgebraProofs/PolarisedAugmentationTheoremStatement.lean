import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.PolarisedAugmentationTheorem
open ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Up GlobalTheory.CompanionTheory.Ar.GR
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.polarised_augmentation_theorem : GlobalTheory.CompanionTheory.Ar.GR.PolarisedAFStatement := by
  first | exact @GlobalTheory.CompanionTheory.Ar.GR.polarisedAF | exact GlobalTheory.CompanionTheory.Ar.GR.polarisedAF | (intros; apply GlobalTheory.CompanionTheory.Ar.GR.polarisedAF <;> assumption)
