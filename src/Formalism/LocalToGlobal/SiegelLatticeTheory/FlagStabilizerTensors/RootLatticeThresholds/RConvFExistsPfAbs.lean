import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.CStarAlgebra.Module.Constructions
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Altitude
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Monotonicity.Lemmas
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Sheaves.Init

noncomputable section

namespace Formalism.L2.SG.Pf.RConvFExistsPf

open MeasureTheory
open scoped InnerProductSpace

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

theorem wk_integrable {U : α → (E →L[ℂ] E)} (hU : ∀ g z, ‖U g z‖ ≤ ‖z‖)
    (hm : ∀ x y : E, AEStronglyMeasurable (fun g => ⟪x, U g y⟫_ℂ) μ) {f : α → ℂ} (hf : Integrable f μ)
    (x y : E) : Integrable (fun g => f g * ⟪x, U g y⟫_ℂ) μ := by
  refine (hf.norm.mul_const (‖x‖ * ‖y‖)).mono' (hf.aestronglyMeasurable.mul (hm x y))
    (Filter.Eventually.of_forall fun g => ?_)
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_left
    ((norm_inner_le_norm x (U g y)).trans (mul_le_mul_of_nonneg_left (hU g y) (norm_nonneg x))) (norm_nonneg _)

theorem wk_bound {U : α → (E →L[ℂ] E)} (hU : ∀ g z, ‖U g z‖ ≤ ‖z‖) {f : α → ℂ} (hf : Integrable f μ)
    (x y : E) : ‖∫ g, f g * ⟪x, U g y⟫_ℂ ∂μ‖ ≤ (∫ g, ‖f g‖ ∂μ) * ‖x‖ * ‖y‖ := by
  calc ‖∫ g, f g * ⟪x, U g y⟫_ℂ ∂μ‖ ≤ ∫ g, ‖f g‖ * (‖x‖ * ‖y‖) ∂μ := by
        refine norm_integral_le_of_norm_le (hf.norm.mul_const _) (Filter.Eventually.of_forall fun g => ?_)
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_left
          ((norm_inner_le_norm x (U g y)).trans (mul_le_mul_of_nonneg_left (hU g y) (norm_nonneg x)))
          (norm_nonneg _)
    _ = (∫ g, ‖f g‖ ∂μ) * ‖x‖ * ‖y‖ := by rw [integral_mul_const, mul_assoc]

def wkForm {U : α → (E →L[ℂ] E)} (hU : ∀ g z, ‖U g z‖ ≤ ‖z‖)
    (hm : ∀ x y : E, AEStronglyMeasurable (fun g => ⟪x, U g y⟫_ℂ) μ) {f : α → ℂ} (hf : Integrable f μ) :
    E →L⋆[ℂ] E →L[ℂ] ℂ :=
  LinearMap.mkContinuous₂
    (LinearMap.mk₂'ₛₗ (starRingEnd ℂ) (RingHom.id ℂ) (fun x y => ∫ g, f g * ⟪x, U g y⟫_ℂ ∂μ)
      (fun x₁ x₂ y => by
        simp only [inner_add_left, mul_add]
        exact integral_add (wk_integrable hU hm hf x₁ y) (wk_integrable hU hm hf x₂ y))
      (fun c x y => by
        simp only [inner_smul_left, smul_eq_mul]
        rw [← integral_const_mul]
        congr 1; funext g; ring)
      (fun x y₁ y₂ => by
        simp only [map_add, inner_add_right, mul_add]
        exact integral_add (wk_integrable hU hm hf x y₁) (wk_integrable hU hm hf x y₂))
      (fun c x y => by
        simp only [map_smul, inner_smul_right, smul_eq_mul, RingHom.id_apply]
        rw [← integral_const_mul]
        congr 1; funext g; ring))
    (∫ g, ‖f g‖ ∂μ) (fun x y => wk_bound hU hf x y)

theorem wk_exists {U : α → (E →L[ℂ] E)} (hU : ∀ g z, ‖U g z‖ ≤ ‖z‖)
    (hm : ∀ x y : E, AEStronglyMeasurable (fun g => ⟪x, U g y⟫_ℂ) μ) {f : α → ℂ} (hf : Integrable f μ) :
    ∃ T : E →L[ℂ] E, ∀ x y : E, ⟪x, T y⟫_ℂ = ∫ g, f g * ⟪x, U g y⟫_ℂ ∂μ := by
  refine ⟨ContinuousLinearMap.adjoint (InnerProductSpace.continuousLinearMapOfBilin (wkForm hU hm hf)),
    fun x y => ?_⟩
  rw [ContinuousLinearMap.adjoint_inner_right, InnerProductSpace.continuousLinearMapOfBilin_apply]
  rfl

end Formalism.L2.SG.Pf.RConvFExistsPf
