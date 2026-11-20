import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsCuspExpansionDiscriminantIntegerLeadingOne
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_cuspExpansion_discriminant_integer_leading_one : ∀ (Ω : Type) [Field Ω] (ε : Ω →+* ℂ), ∃ h : HahnSeries ℚ Ω, IsExp ε DD h ∧ h ≠ 0 ∧ h.leadingCoeff = 1 ∧ ∀ r : ℚ, ∃ n : ℤ, h.coeff r = n := by
  first | exact @GlobalTheory.FNExpD.expD | exact GlobalTheory.FNExpD.expD | (intros; apply GlobalTheory.FNExpD.expD <;> assumption)
