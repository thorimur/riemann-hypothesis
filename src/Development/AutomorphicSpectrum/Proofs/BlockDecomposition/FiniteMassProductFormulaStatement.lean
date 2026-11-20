import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiniteMassProductFormula
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_mass_product_formula : PositivityTheory.Rg.BcB.G8.Fin.MassProd := by
  first | exact @GlobalTheory.CompanionTheory.MassProd.massProd | exact GlobalTheory.CompanionTheory.MassProd.massProd | (intros; apply GlobalTheory.CompanionTheory.MassProd.massProd <;> assumption)
