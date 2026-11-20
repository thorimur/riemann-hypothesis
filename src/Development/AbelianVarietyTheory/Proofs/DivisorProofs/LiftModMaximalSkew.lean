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
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
open scoped Matrix

namespace GlobalTheory

theorem lift_mod_maximal_skew : ∀ (O : Type) [CommRing O] [IsLocalRing O] (c : O →+* O), (∀ x, c (c x) = x) → IsUnit (2 : O) →
    ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) O), (∀ i j, c (J j i) = J i j) → IsUnit J.det →
    ∀ Z₀ : Matrix (Fin n) (Fin n) O, (∀ i j, (Z₀ᵀ * J + J * Z₀.map c) i j ∈ IsLocalRing.maximalIdeal O) →
      ∃ Z : Matrix (Fin n) (Fin n) O, Zᵀ * J + J * Z.map c = 0 ∧ ∀ i j, Z i j - Z₀ i j ∈ IsLocalRing.maximalIdeal O := by
  intro O _ _ c hc h2 n J hJ hdet Z₀ hZ
  obtain ⟨u, hu⟩ : ∃ u : O, u * 2 = 1 := ⟨h2.unit⁻¹.val, h2.val_inv_mul⟩
  have hcu : c u = u := by
    have h1 : c u * 2 = 1 := by
      have := congrArg c hu
      simpa [map_mul, map_ofNat] using this
    calc c u = c u * (u * 2) := by rw [hu, mul_one]
      _ = (c u * 2) * u := by ring
      _ = u := by rw [h1, one_mul]
  set E := Z₀ᵀ * J + J * Z₀.map c with hE
  have hJc : (J.map c)ᵀ = J := by
    ext i j; simp [Matrix.transpose_apply, Matrix.map_apply, hJ]
  have hEc : (E.map c)ᵀ = E := by
    ext i j
    simp only [hE, Matrix.transpose_apply, Matrix.map_apply, Matrix.add_apply, Matrix.mul_apply, map_add, map_sum, map_mul, hc, hJ]
    rw [add_comm]
    congr 1 <;> refine Finset.sum_congr rfl (fun k _ => ?_) <;> ring
  have hJinv : J * ((J⁻¹).map c)ᵀ = 1 := by
    calc J * ((J⁻¹).map c)ᵀ = (J.map c)ᵀ * ((J⁻¹).map c)ᵀ := by rw [hJc]
      _ = ((J⁻¹).map c * J.map c)ᵀ := by rw [Matrix.transpose_mul]
      _ = ((J⁻¹ * J).map c)ᵀ := by rw [Matrix.map_mul]
      _ = 1 := by rw [Matrix.nonsing_inv_mul J hdet, Matrix.map_one c c.map_zero c.map_one, Matrix.transpose_one]
  set D := (u • (E * J⁻¹))ᵀ with hD
  have hDT : Dᵀ * J = u • E := by
    rw [hD, Matrix.transpose_transpose, Matrix.smul_mul, Matrix.mul_assoc, Matrix.nonsing_inv_mul J hdet, Matrix.mul_one]
  have hDmap : D.map c = u • (((J⁻¹).map c)ᵀ * (E.map c)ᵀ) := by
    rw [← Matrix.transpose_mul, ← Matrix.map_mul, hD]
    ext i j
    simp [Matrix.transpose_apply, Matrix.map_apply, Matrix.smul_apply, Matrix.mul_apply, map_sum, map_mul, hcu]
  have hDc : J * D.map c = u • E := by
    rw [hDmap, Matrix.mul_smul, ← Matrix.mul_assoc, hJinv, Matrix.one_mul, hEc]
  refine ⟨Z₀ - D, ?_, ?_⟩
  · have hmap : (Z₀ - D).map c = Z₀.map c - D.map c := by
      ext i j; simp [Matrix.map_apply]
    rw [Matrix.transpose_sub, Matrix.sub_mul, hmap, Matrix.mul_sub, hDT, hDc]
    have : E - u • E - u • E = 0 := by
      rw [sub_sub, ← add_smul, ← two_mul, mul_comm, hu, one_smul, sub_self]
    rw [← this, hE]; abel
  · intro i j
    have : (Z₀ - D) i j - Z₀ i j = -(u * ∑ k, E j k * J⁻¹ k i) := by
      simp [hD, Matrix.transpose_apply, Matrix.mul_apply, Matrix.smul_apply, mul_comm]
    rw [this]
    exact neg_mem (Ideal.mul_mem_left _ _ (Ideal.sum_mem _ (fun k _ => Ideal.mul_mem_right _ _ (hZ j k))))

end GlobalTheory
