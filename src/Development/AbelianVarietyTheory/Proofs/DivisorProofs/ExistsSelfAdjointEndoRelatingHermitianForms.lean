import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Altitude
import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.SimpleRing.Principal
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
open Matrix

namespace GlobalTheory

theorem herm_gamma_star_map_mulVec {g : ℕ} (M : Matrix (Fin g) (Fin g) ℂ) (v : Fin g → ℂ) :
    star (M.map star *ᵥ v) = M *ᵥ star v := by
  funext i
  simp only [mulVec, dotProduct, Pi.star_apply, star_sum, map_apply, star_mul', star_star]

theorem herm_gamma_map_mulVec_dot {g : ℕ} (B : Matrix (Fin g) (Fin g) ℂ) (z u : Fin g → ℂ) :
    (B *ᵥ z) ⬝ᵥ u = z ⬝ᵥ (Bᵀ *ᵥ u) := by
  rw [dotProduct_comm, dotProduct_mulVec, mulVec_transpose, dotProduct_comm]

theorem herm_gamma_det_ne_zero {g : ℕ} (H₁ : Matrix (Fin g) (Fin g) ℂ)
    (hpos : ∀ z : Fin g → ℂ, z ≠ 0 → 0 < (z ⬝ᵥ H₁.mulVec (star z)).re) : H₁.det ≠ 0 := by
  intro hdet
  obtain ⟨v, hv, hHv⟩ := (Matrix.exists_mulVec_eq_zero_iff).2 hdet
  have hz : star v ≠ 0 := by
    intro h; apply hv; simpa using congrArg star h
  have := hpos (star v) hz
  rw [star_star, hHv, dotProduct_zero] at this
  simp at this

theorem herm_gamma : ∀ (g : ℕ) (H₁ H₂ : Matrix (Fin g) (Fin g) ℂ), H₁.IsHermitian → H₂.IsHermitian →
    (∀ z : Fin g → ℂ, z ≠ 0 → 0 < (z ⬝ᵥ H₁.mulVec (star z)).re) →
    ∃ γ : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ),
      (∀ z w, z ⬝ᵥ H₂.mulVec (star w) = z ⬝ᵥ H₁.mulVec (star (γ w))) ∧
      ∀ z w, z ⬝ᵥ H₂.mulVec (star (γ w)) = γ z ⬝ᵥ H₂.mulVec (star w) := by
  intro g H₁ H₂ h1 h2 hpos
  have hdet : IsUnit H₁.det := isUnit_iff_ne_zero.2 (herm_gamma_det_ne_zero H₁ hpos)
  refine ⟨Matrix.toLin' ((H₁⁻¹ * H₂).map star), ?_, ?_⟩
  · intro z w
    rw [Matrix.toLin'_apply, herm_gamma_star_map_mulVec, mulVec_mulVec, ← Matrix.mul_assoc,
      Matrix.mul_nonsing_inv _ hdet, Matrix.one_mul]
  · intro z w
    rw [Matrix.toLin'_apply, Matrix.toLin'_apply, herm_gamma_star_map_mulVec, mulVec_mulVec,
      herm_gamma_map_mulVec_dot, mulVec_mulVec]
    congr 2
    have hT : ((H₁⁻¹ * H₂).map star)ᵀ = (H₁⁻¹ * H₂)ᴴ := rfl
    rw [hT, conjTranspose_mul, h2.eq, conjTranspose_nonsing_inv, h1.eq, Matrix.mul_assoc]

end GlobalTheory
