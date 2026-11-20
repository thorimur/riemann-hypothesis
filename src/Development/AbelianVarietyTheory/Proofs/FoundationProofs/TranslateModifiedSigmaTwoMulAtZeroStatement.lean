import Development.AbelianVarietyTheory.Proofs.FoundationProofs.TranslateModifiedSigmaTwoMulAtZero
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.translate_modifiedSigma_two_mul_at_zero : ∀ (Λ : AddSubgroup ℂ), GlobalTheory.EvenTheta.IsLat Λ → ∀ P : ℂ, P ∉ Λ → U1 Λ (2 * P) (sgStar Λ) 0 = -(wpD Λ P) * U1 Λ P (sgStar Λ) 0 ^ 4 := by
  first | exact @GlobalTheory.SigmaDuplication.U1_two_mul_at_zero_eq_neg_wpD_mul_pow_four | exact GlobalTheory.SigmaDuplication.U1_two_mul_at_zero_eq_neg_wpD_mul_pow_four | (intros; apply GlobalTheory.SigmaDuplication.U1_two_mul_at_zero_eq_neg_wpD_mul_pow_four <;> assumption)
