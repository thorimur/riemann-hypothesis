import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HasQExpansionSumAboveMul
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hasQExpansionSumAbove_mul : ∀ (Ω : Type) [Field Ω] (ε : Ω →+* ℂ) (C : ℝ) (φ ψ : ℂ → ℂ) (h h' : HahnSeries ℚ Ω), HS ε C φ h → HS ε C ψ h' → HS ε C (φ * ψ) (h * h') := by
  first | exact @GlobalTheory.FNProd.hs_mul | exact GlobalTheory.FNProd.hs_mul | (intros; apply GlobalTheory.FNProd.hs_mul <;> assumption)
