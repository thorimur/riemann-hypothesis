import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OneVectorFormulaOfParts
open PositivityTheory.Rg.Mass
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.one_vector_formula_of_parts : Prop1 → Simil → Hasse → Cnt → E1 := by
  first | exact @GlobalTheory.CompanionTheory.Mass.anisotropic_binary_one_vector_formula | exact GlobalTheory.CompanionTheory.Mass.anisotropic_binary_one_vector_formula | (intros; apply GlobalTheory.CompanionTheory.Mass.anisotropic_binary_one_vector_formula <;> assumption)
