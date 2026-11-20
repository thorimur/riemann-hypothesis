import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DoubleComplexClassSurjective
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris DividedPowers GlobalTheory.CechDR GlobalTheory.HodgeCoh CrystallineSemistableComparison CrystallineSemistableComparison.Pb CrystallineSemistableComparison.Om CrystallineSemistableComparison.Om.Glob GlobalTheory.CompanionTheory.CechSerre
universe w
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.double_complex_class_surjective : ∀ {R : Type} [CommRing R] (K : DCx.{w} R) (a j : ℕ), (∀ p q, a < q → Subsingleton ((K.col p).H q)) →
    Function.Surjective (clsZ K (a + j) j) := by
  first | exact @GlobalTheory.CompanionTheory.CechSerre.clsZ_surjective_of_acyclic | exact GlobalTheory.CompanionTheory.CechSerre.clsZ_surjective_of_acyclic | (intros; apply GlobalTheory.CompanionTheory.CechSerre.clsZ_surjective_of_acyclic <;> assumption)
