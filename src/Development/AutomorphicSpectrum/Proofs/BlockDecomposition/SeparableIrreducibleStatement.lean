import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SeparableIrreducible
open ReciprocityTheory.Ty.Fin
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.separable_irreducible : ReciprocityTheory.Ty.Fin.St.SepIrr := by
  first | exact @GlobalTheory.CompanionTheory.FinRep.sepIrr | exact GlobalTheory.CompanionTheory.FinRep.sepIrr | (intros; apply GlobalTheory.CompanionTheory.FinRep.sepIrr <;> assumption)
