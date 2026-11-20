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
import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
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

theorem rat_alternating_orthogonal_orthogonal_le :
    ∀ (r : ℕ) (Mq : Matrix (Fin r) (Fin r) ℚ) (V : Submodule ℚ (Fin r → ℚ)), Mqᵀ = -Mq →
      Mq.det ≠ 0 → ∀ x : Fin r → ℚ,
      (∀ y : Fin r → ℚ, (∀ w ∈ V, y ⬝ᵥ Mq *ᵥ w = 0) → x ⬝ᵥ Mq *ᵥ y = 0) → x ∈ V := by
  intro r Mq V hT hdet x hx
  have hB : ∀ u v : Fin r → ℚ, Matrix.toBilin' Mq u v = u ⬝ᵥ Mq *ᵥ v :=
    fun u v => Matrix.toBilin'_apply' Mq u v
  have hanti : ∀ u v : Fin r → ℚ, u ⬝ᵥ Mq *ᵥ v = -(v ⬝ᵥ Mq *ᵥ u) := by
    intro u v
    have h1 : v ⬝ᵥ Mqᵀ *ᵥ u = u ⬝ᵥ Mq *ᵥ v := by
      rw [Matrix.mulVec_transpose, dotProduct_comm, ← Matrix.dotProduct_mulVec]
    rw [← h1, hT, Matrix.neg_mulVec, dotProduct_neg]
  have hrefl : (Matrix.toBilin' Mq).IsRefl := by
    intro u v h
    rw [hB] at h ⊢
    rw [hanti, h, neg_zero]
  have hnd : (Matrix.toBilin' Mq).Nondegenerate :=
    LinearMap.BilinForm.nondegenerate_toBilin'_iff_det_ne_zero.mpr hdet
  rw [← LinearMap.BilinForm.orthogonal_orthogonal hnd hrefl V,
    LinearMap.BilinForm.mem_orthogonal_iff]
  intro y hy
  rw [LinearMap.BilinForm.mem_orthogonal_iff] at hy
  show Matrix.toBilin' Mq y x = 0
  rw [hB, hanti, hx y ?_, neg_zero]
  intro w hw
  have h := hy w hw
  change Matrix.toBilin' Mq w y = 0 at h
  rw [hB, hanti] at h
  exact neg_eq_zero.mp h

end GlobalTheory
