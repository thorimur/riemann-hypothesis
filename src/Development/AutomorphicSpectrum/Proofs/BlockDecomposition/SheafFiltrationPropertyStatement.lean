import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SheafFiltrationProperty
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sheaf_filtration_property : ∀ {b : Base} {L : b.Fun} (Q : ObjectProperty (Thick L)), IsFil (sP Q) (sFil Q) := by
  first | exact @GlobalTheory.CompanionTheory.DPFil.isFil_sFil | exact GlobalTheory.CompanionTheory.DPFil.isFil_sFil | (intros; apply GlobalTheory.CompanionTheory.DPFil.isFil_sFil <;> assumption)
