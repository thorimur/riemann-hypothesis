import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
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
import Mathlib.Tactic.ENatToNat
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Presheaf

open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct

namespace GlobalTheory.ClassFin

theorem log_sq_le_tangent_add_sq :
    ∀ a : ℝ, 0 < a → ∃ C : ℝ, 0 ≤ C ∧ ∀ x y : ℝ, a ≤ x → a ≤ y →
      (Real.log y) ^ 2 ≤ (Real.log x) ^ 2 + 2 * Real.log x / x * (y - x) + C * (y - x) ^ 2 := by
  intro a ha
  refine ⟨(2 + 2 * |Real.log a|) / a ^ 2, by positivity, ?_⟩
  intro x y hx hy
  have hx0 : 0 < x := lt_of_lt_of_le ha hx
  have hy0 : 0 < y := lt_of_lt_of_le ha hy
  obtain ⟨d, hd⟩ : ∃ d : ℝ, d = Real.log y - Real.log x := ⟨_, rfl⟩
  have hlogy : Real.log y = Real.log x + d := by rw [hd]; ring
  have hup : d ≤ (y - x) / x := by
    have h := Real.log_le_sub_one_of_pos (div_pos hy0 hx0)
    rw [Real.log_div hy0.ne' hx0.ne'] at h
    have e : y / x - 1 = (y - x) / x := by field_simp
    rw [hd]; linarith
  have hlow : (y - x) / y ≤ d := by
    have h := Real.log_le_sub_one_of_pos (div_pos hx0 hy0)
    rw [Real.log_div hx0.ne' hy0.ne'] at h
    have e : (y - x) / y = 1 - x / y := by field_simp
    rw [hd, e]; linarith
  have hxy : a ^ 2 ≤ x * y := by nlinarith
  have hxx : a ^ 2 ≤ x ^ 2 := by nlinarith
  have hyy : a ^ 2 ≤ y ^ 2 := by nlinarith
  have ha2 : 0 < a ^ 2 := by positivity
  have hK0 : 0 ≤ (y - x) ^ 2 / a ^ 2 := by positivity
  have hgap : (y - x) / x - d ≤ (y - x) ^ 2 / a ^ 2 := by
    have e : (y - x) / x - (y - x) / y = (y - x) ^ 2 / (x * y) := by
      field_simp
    have h : (y - x) ^ 2 / (x * y) ≤ (y - x) ^ 2 / a ^ 2 :=
      div_le_div_of_nonneg_left (sq_nonneg _) ha2 hxy
    linarith
  have hq2 : ((y - x) / x) ^ 2 ≤ (y - x) ^ 2 / a ^ 2 := by
    rw [div_pow]; exact div_le_div_of_nonneg_left (sq_nonneg _) ha2 hxx
  have hp2 : ((y - x) / y) ^ 2 ≤ (y - x) ^ 2 / a ^ 2 := by
    rw [div_pow]; exact div_le_div_of_nonneg_left (sq_nonneg _) ha2 hyy
  have hd2 : d ^ 2 ≤ 2 * ((y - x) ^ 2 / a ^ 2) := by
    rcases le_total 0 d with h | h
    · nlinarith [sq_nonneg ((y - x) / y)]
    · nlinarith [sq_nonneg ((y - x) / x)]
  have hu : -Real.log x ≤ |Real.log a| := by
    have := Real.log_le_log ha hx
    have := neg_le_abs (Real.log a)
    linarith
  have hL0 : 0 ≤ |Real.log a| := abs_nonneg _
  have he0 : 0 ≤ (y - x) / x - d := by linarith
  have h3 : -Real.log x * ((y - x) / x - d) ≤ |Real.log a| * ((y - x) ^ 2 / a ^ 2) :=
    le_trans (mul_le_mul_of_nonneg_right hu he0) (mul_le_mul_of_nonneg_left hgap hL0)
  have e1 : 2 * Real.log x / x * (y - x) = 2 * Real.log x * ((y - x) / x) := by ring
  have e2 : (2 + 2 * |Real.log a|) / a ^ 2 * (y - x) ^ 2
      = (2 + 2 * |Real.log a|) * ((y - x) ^ 2 / a ^ 2) := by ring
  rw [hlogy, e1, e2]
  nlinarith [h3, hd2]

end GlobalTheory.ClassFin
