import Development.AbelianVarietyTheory.Proofs.DivisorProofs.G2AddWeierstrassPRowSum
open scoped UpperHalfPlane MatrixGroups Matrix ModularForm ComplexConjugate
open GlobalTheory.QFam GlobalTheory.WpFam
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.G2_add_weierstrassP_row_sum : ∀ (τ : ℍ) (z : ℂ), HasSum (fun n : ℤ => ∑' m : ℤ, 1 / (z + n * (τ : ℂ) + m) ^ 2) (EisensteinSeries.G2 τ + (tauPair τ).weierstrassP z) := by
  first | exact @GlobalTheory.WpFam.hasSum_rows_G2_add_weierstrassP | exact GlobalTheory.WpFam.hasSum_rows_G2_add_weierstrassP | (intros; apply GlobalTheory.WpFam.hasSum_rows_G2_add_weierstrassP <;> assumption)
