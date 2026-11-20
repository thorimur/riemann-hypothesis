import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HarishChandraDimension
open ReciprocityTheory.Ty.Fin
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.harish_chandra_dimension : ReciprocityTheory.Ty.Fin.St.HCDim := by
  first | exact @GlobalTheory.CompanionTheory.TyFin.hcDim | exact GlobalTheory.CompanionTheory.TyFin.hcDim | (intros; apply GlobalTheory.CompanionTheory.TyFin.hcDim <;> assumption)
