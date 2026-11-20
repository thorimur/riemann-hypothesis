import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsCuspExpansionAtInfinityCompRatAffine
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isCuspExpansionAtInfinity_comp_rat_affine : ∀ (Ω : Type) [Field Ω] (ε : Ω →+* ℂ) (f f' : ℍ → ℂ) (l m : ℚ) (h h' : HahnSeries ℚ Ω), 0 < l → (∀ z ∈ Hs, up f' z = up f ((l : ℂ) * z + m)) → (∀ r : ℚ, ε (h'.coeff (r * l)) = Complex.exp (2 * Real.pi * Complex.I * ((r * m : ℚ) : ℂ)) * ε (h.coeff r)) → IsExp ε f h → IsExp ε f' h' := by
  first | exact @GlobalTheory.FN.isExp_comp_affine | exact GlobalTheory.FN.isExp_comp_affine | (intros; apply GlobalTheory.FN.isExp_comp_affine <;> assumption)
