import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DoubleComplexLeadZeroOfClassZero
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris DividedPowers GlobalTheory.CechDR GlobalTheory.HodgeCoh CrystallineSemistableComparison CrystallineSemistableComparison.Pb CrystallineSemistableComparison.Om CrystallineSemistableComparison.Om.Glob GlobalTheory.CompanionTheory.CechSerre
universe w
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.double_complex_lead_zero_of_class_zero : ∀ {R : Type} [CommRing R] (K : DCx.{w} R) (a j : ℕ), (∀ p q, a < q → Subsingleton ((K.col p).H q)) →
    ∀ z : Zf K (a + j) j, clsZ K (a + j) j z = 0 → leadE K j a z = 0 := by
  first | exact @GlobalTheory.CompanionTheory.CechSerre.RowKer.leadE_eq_zero | exact GlobalTheory.CompanionTheory.CechSerre.RowKer.leadE_eq_zero | (intros; apply GlobalTheory.CompanionTheory.CechSerre.RowKer.leadE_eq_zero <;> assumption)
