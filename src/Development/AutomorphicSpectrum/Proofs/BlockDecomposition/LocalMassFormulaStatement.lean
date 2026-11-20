import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalMassFormula
open PositivityTheory.Rg.Mass
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_mass_formula : LocMass := by
  first | exact @GlobalTheory.CompanionTheory.SW.LocBin.locMass | exact GlobalTheory.CompanionTheory.SW.LocBin.locMass | (intros; apply GlobalTheory.CompanionTheory.SW.LocBin.locMass <;> assumption)
