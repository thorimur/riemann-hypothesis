import Development.AbelianVarietyTheory.Proofs.FoundationProofs.MonicRootNormLeOneAddSum
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.norm_root_le_one_add_sum_norm_coeff : ∀ (n : ℕ) (s : Fin n → ℂ) (y : ℂ), y ^ n + ∑ j, s j * y ^ (j : ℕ) = 0 → ‖y‖ ≤ 1 + ∑ j, ‖s j‖ := by
  first | exact @GlobalTheory.monic_root_norm_le_one_add_sum | exact GlobalTheory.monic_root_norm_le_one_add_sum | (intros; apply GlobalTheory.monic_root_norm_le_one_add_sum <;> assumption)
