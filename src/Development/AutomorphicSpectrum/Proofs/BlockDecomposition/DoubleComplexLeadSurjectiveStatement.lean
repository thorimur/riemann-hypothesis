import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DoubleComplexLeadSurjective
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris DividedPowers GlobalTheory.CechDR GlobalTheory.HodgeCoh CrystallineSemistableComparison CrystallineSemistableComparison.Pb CrystallineSemistableComparison.Om CrystallineSemistableComparison.Om.Glob GlobalTheory.CompanionTheory.CechSerre
universe w
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.double_complex_lead_surjective : ∀ {R : Type} [CommRing R] (K : DCx.{w} R) (a j : ℕ), (∀ p q, q < a → Subsingleton ((K.col p).H q)) →
    Function.Surjective (leadE K j a (n := a + j)) := by
  first | exact @GlobalTheory.CompanionTheory.CechSerre.leadE_surjective | exact GlobalTheory.CompanionTheory.CechSerre.leadE_surjective | (intros; apply GlobalTheory.CompanionTheory.CechSerre.leadE_surjective <;> assumption)
