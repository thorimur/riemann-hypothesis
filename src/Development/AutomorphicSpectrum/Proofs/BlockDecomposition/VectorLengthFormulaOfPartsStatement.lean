import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.VectorLengthFormulaOfParts
open PositivityTheory.Rg.Mass
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.vector_length_formula_of_parts : CoCpt → LocMass → Prop1 := by
  first | exact @GlobalTheory.CompanionTheory.Mass.One.vector_length_formula_up_to_constant | exact GlobalTheory.CompanionTheory.Mass.One.vector_length_formula_up_to_constant | (intros; apply GlobalTheory.CompanionTheory.Mass.One.vector_length_formula_up_to_constant <;> assumption)
