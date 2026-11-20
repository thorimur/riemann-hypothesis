import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.BruhatDecompositionUnique
open ReciprocityTheory.Ty.Fin
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.bruhat_decomposition_unique : ReciprocityTheory.Ty.Fin.St.BruhatUniq := by
  first | exact @GlobalTheory.CompanionTheory.BruhatInv.bruhatUniq | exact GlobalTheory.CompanionTheory.BruhatInv.bruhatUniq | (intros; apply GlobalTheory.CompanionTheory.BruhatInv.bruhatUniq <;> assumption)
