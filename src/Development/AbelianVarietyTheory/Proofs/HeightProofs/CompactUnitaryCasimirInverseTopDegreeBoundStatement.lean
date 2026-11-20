import Development.AbelianVarietyTheory.Proofs.HeightProofs.CompactUnitaryCasimirInverseTopDegreeBound
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Matrix
open Formalism.REAL GlobalTheory.SmoothGlob GlobalTheory.TypeSum
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.KFourier MeasureTheory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.compactUnitaryCasimir_inverse_topDegree_bound : ∀ {n : ℕ} (ε : Fin n → Bool) {r : ℕ} (X : Fin r → Mx n), (∀ j, inK ε (X j)) → ∀ (i : ℕ) (l : ℝ), 0 < l → (∀ p ∈ polyV ε i, (∀ q ∈ lowV ε i, ∫ k, q k * p k ∂(muK ε) = 0) → l * ∫ k, ‖p k‖ ^ 2 ∂(muK ε) ≤ ∑ j, ∫ k, ‖rder ε [X j] p k‖ ^ 2 ∂(muK ε)) → ∀ (M : ℕ) (e : KG ε → ℂ), e ∈ polyV ε i → (∀ q ∈ lowV ε i, ∫ k, q k * e k ∂(muK ε) = 0) → ∃ s ∈ polyV ε i, (fun φ : KG ε → ℂ => ∑ j, rder ε [X j, X j] φ)^[M] s = e ∧ ∫ k, ‖s k‖ ^ 2 ∂(muK ε) ≤ (l ^ (2 * M))⁻¹ * ∫ k, ‖e k‖ ^ 2 ∂(muK ε) := by
  first | exact @GlobalTheory.KFourier.casimir_inverse_bound | exact GlobalTheory.KFourier.casimir_inverse_bound | (intros; apply GlobalTheory.KFourier.casimir_inverse_bound <;> assumption)
