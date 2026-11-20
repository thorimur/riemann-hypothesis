import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsIntegralCuspExpansionJInvariant
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_integral_cuspExpansion_jInvariant : ∀ (Ω : Type) [Field Ω] (ε : Ω →+* ℂ), ∃ h : HahnSeries ℚ Ω, IsExp ε jT h ∧ h.coeff (-1) = 1 ∧ (∀ r : ℚ, r < -1 → h.coeff r = 0) ∧ ∀ r : ℚ, ∃ n : ℤ, h.coeff r = n := by
  first | exact @GlobalTheory.FNExpJ.expansion_j | exact GlobalTheory.FNExpJ.expansion_j | (intros; apply GlobalTheory.FNExpJ.expansion_j <;> assumption)
