import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GradedFormCocycle
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.graded_form_cocycle : GlobalTheory.CompanionTheory.GrForm.StCocycle := by
  first | exact @GlobalTheory.CompanionTheory.GrForm.stCocycle | exact GlobalTheory.CompanionTheory.GrForm.stCocycle | (intros; apply GlobalTheory.CompanionTheory.GrForm.stCocycle <;> assumption)
