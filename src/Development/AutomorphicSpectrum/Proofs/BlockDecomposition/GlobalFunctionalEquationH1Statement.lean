import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GlobalFunctionalEquationH1
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.global_functional_equation_h1 : Ad3.R.B0 → Ad3.R.E2 → Ad3.R.H1 := by
  first | exact @GlobalTheory.CompanionTheory.HeckePartial.partial_functional_equation | exact GlobalTheory.CompanionTheory.HeckePartial.partial_functional_equation | (intros; apply GlobalTheory.CompanionTheory.HeckePartial.partial_functional_equation <;> assumption)
