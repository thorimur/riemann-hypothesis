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

namespace Formalism.MainNotions.N.FrobeniusPowerSeries.NumericInequalities

variable {x : ℝ}

lemma u_le (hx : 11 ≤ x) : x⁻¹ ≤ 1 / 11 := by
  have h0 : 0 < x := by linarith
  have h1 : 0 < x - 1 := by linarith
  have h2 : 0 < x - 2 := by linarith
  have h : 0 ≤ x - 11 := by linarith
  have n0 : x ≠ 0 := h0.ne'
  have n1 : x - 1 ≠ 0 := h1.ne'
  have n2 : x - 2 ≠ 0 := h2.ne'
  have e : 1 / 11 - x⁻¹ = (x - 11) / (11 * x) := by
    field_simp <;> ring
  have hd : 0 ≤ 1 / 11 - x⁻¹ := by
    rw [e]
    exact div_nonneg (by linarith) (mul_nonneg (by norm_num) h0.le)
  linarith

lemma p_le (hx : 11 ≤ x) : (x - 1)⁻¹ ≤ 1 / 10 := by
  have h0 : 0 < x := by linarith
  have h1 : 0 < x - 1 := by linarith
  have h2 : 0 < x - 2 := by linarith
  have h : 0 ≤ x - 11 := by linarith
  have n0 : x ≠ 0 := h0.ne'
  have n1 : x - 1 ≠ 0 := h1.ne'
  have n2 : x - 2 ≠ 0 := h2.ne'
  have e : 1 / 10 - (x - 1)⁻¹ = (x - 11) / (10 * (x - 1)) := by
    field_simp <;> ring
  have hd : 0 ≤ 1 / 10 - (x - 1)⁻¹ := by
    rw [e]
    exact div_nonneg (by linarith) (mul_nonneg (by norm_num) h1.le)
  linarith

lemma e_le (hx : 11 ≤ x) : (x - 2)⁻¹ ≤ 1 / 9 := by
  have h0 : 0 < x := by linarith
  have h1 : 0 < x - 1 := by linarith
  have h2 : 0 < x - 2 := by linarith
  have h : 0 ≤ x - 11 := by linarith
  have n0 : x ≠ 0 := h0.ne'
  have n1 : x - 1 ≠ 0 := h1.ne'
  have n2 : x - 2 ≠ 0 := h2.ne'
  have e : 1 / 9 - (x - 2)⁻¹ = (x - 11) / (9 * (x - 2)) := by
    field_simp <;> ring
  have hd : 0 ≤ 1 / 9 - (x - 2)⁻¹ := by
    rw [e]
    exact div_nonneg (by linarith) (mul_nonneg (by norm_num) h2.le)
  linarith

lemma u_le_p (hx : 11 ≤ x) : x⁻¹ ≤ (x - 1)⁻¹ := by
  have h0 : 0 < x := by linarith
  have h1 : 0 < x - 1 := by linarith
  have h2 : 0 < x - 2 := by linarith
  have h : 0 ≤ x - 11 := by linarith
  have n0 : x ≠ 0 := h0.ne'
  have n1 : x - 1 ≠ 0 := h1.ne'
  have n2 : x - 2 ≠ 0 := h2.ne'
  have e : (x - 1)⁻¹ - x⁻¹ = 1 / (x * (x - 1)) := by
    field_simp <;> ring
  have hd : 0 ≤ (x - 1)⁻¹ - x⁻¹ := by
    rw [e]
    exact div_nonneg (zero_le_one) (mul_nonneg h0.le h1.le)
  linarith

lemma q_le (hx : 11 ≤ x) : x / (x - 1) ^ 2 ≤ 121 / 100 * x⁻¹ := by
  have h0 : 0 < x := by linarith
  have h1 : 0 < x - 1 := by linarith
  have h2 : 0 < x - 2 := by linarith
  have h : 0 ≤ x - 11 := by linarith
  have n0 : x ≠ 0 := h0.ne'
  have n1 : x - 1 ≠ 0 := h1.ne'
  have n2 : x - 2 ≠ 0 := h2.ne'
  have e : 121 / 100 * x⁻¹ - x / (x - 1) ^ 2 = (21 * x ^ 2 - 242 * x + 121) / (100 * x * (x - 1) ^ 2) := by
    field_simp <;> ring
  have hd : 0 ≤ 121 / 100 * x⁻¹ - x / (x - 1) ^ 2 := by
    rw [e]
    exact div_nonneg (by nlinarith [h, mul_nonneg h h]) (mul_nonneg (mul_nonneg (by norm_num) h0.le) (sq_nonneg _))
  linarith

lemma e_le_u (hx : 11 ≤ x) : (x - 2)⁻¹ ≤ 11 / 9 * x⁻¹ := by
  have h0 : 0 < x := by linarith
  have h1 : 0 < x - 1 := by linarith
  have h2 : 0 < x - 2 := by linarith
  have h : 0 ≤ x - 11 := by linarith
  have n0 : x ≠ 0 := h0.ne'
  have n1 : x - 1 ≠ 0 := h1.ne'
  have n2 : x - 2 ≠ 0 := h2.ne'
  have e : 11 / 9 * x⁻¹ - (x - 2)⁻¹ = (2 * x - 22) / (9 * x * (x - 2)) := by
    field_simp <;> ring
  have hd : 0 ≤ 11 / 9 * x⁻¹ - (x - 2)⁻¹ := by
    rw [e]
    exact div_nonneg (by linarith) (mul_nonneg (mul_nonneg (by norm_num) h0.le) h2.le)
  linarith

lemma p_le_u (hx : 11 ≤ x) : (x - 1)⁻¹ ≤ 11 / 10 * x⁻¹ := by
  have h0 : 0 < x := by linarith
  have h1 : 0 < x - 1 := by linarith
  have h2 : 0 < x - 2 := by linarith
  have h : 0 ≤ x - 11 := by linarith
  have n0 : x ≠ 0 := h0.ne'
  have n1 : x - 1 ≠ 0 := h1.ne'
  have n2 : x - 2 ≠ 0 := h2.ne'
  have e : 11 / 10 * x⁻¹ - (x - 1)⁻¹ = (x - 11) / (10 * x * (x - 1)) := by
    field_simp <;> ring
  have hd : 0 ≤ 11 / 10 * x⁻¹ - (x - 1)⁻¹ := by
    rw [e]
    exact div_nonneg (by linarith) (mul_nonneg (mul_nonneg (by norm_num) h0.le) h1.le)
  linarith

lemma inv_sub_one_sq_le_inv (hx : 11 ≤ x) : (x - 1)⁻¹ ^ 2 ≤ x⁻¹ := by
  have h0 : 0 < x := by linarith
  have h1 : 0 < x - 1 := by linarith
  have h2 : 0 < x - 2 := by linarith
  have h : 0 ≤ x - 11 := by linarith
  have n0 : x ≠ 0 := h0.ne'
  have n1 : x - 1 ≠ 0 := h1.ne'
  have n2 : x - 2 ≠ 0 := h2.ne'
  have e : x⁻¹ - (x - 1)⁻¹ ^ 2 = (x ^ 2 - 3 * x + 1) / (x * (x - 1) ^ 2) := by
    field_simp <;> ring
  have hd : 0 ≤ x⁻¹ - (x - 1)⁻¹ ^ 2 := by
    rw [e]
    exact div_nonneg (by nlinarith [h, mul_nonneg h h]) (mul_nonneg h0.le (sq_nonneg _))
  linarith

lemma k_cut (hx : 11 ≤ x) :
    (x - 1)⁻¹ - x⁻¹ + (x - 1)⁻¹ ^ 2 * (x - 2)⁻¹ ≤ 5 / 4 * x⁻¹ ^ 2 := by
  have h0 : 0 < x := by linarith
  have h1 : 0 < x - 1 := by linarith
  have h2 : 0 < x - 2 := by linarith
  have h : 0 ≤ x - 11 := by linarith
  have n0 : x ≠ 0 := h0.ne'
  have n1 : x - 1 ≠ 0 := h1.ne'
  have n2 : x - 2 ≠ 0 := h2.ne'
  have e : 5 / 4 * x⁻¹ ^ 2 - ((x - 1)⁻¹ - x⁻¹ + (x - 1)⁻¹ ^ 2 * (x - 2)⁻¹) = (x ^ 3 - 12 * x ^ 2 + 17 * x - 10) / (4 * x ^ 2 * (x - 1) ^ 2 * (x - 2)) := by
    field_simp <;> ring
  have hd : 0 ≤ 5 / 4 * x⁻¹ ^ 2 - ((x - 1)⁻¹ - x⁻¹ + (x - 1)⁻¹ ^ 2 * (x - 2)⁻¹) := by
    rw [e]
    exact div_nonneg (by nlinarith [h, mul_nonneg h h, mul_nonneg (mul_nonneg h h) h]) (mul_nonneg (mul_nonneg (by positivity) (sq_nonneg _)) h2.le)
  linarith

lemma k_le (hx : 11 ≤ x) :
    (x - 1)⁻¹ - x⁻¹ + (x - 1)⁻¹ * (x - 2)⁻¹ ≤ 22 / 9 * x⁻¹ ^ 2 := by
  have h0 : 0 < x := by linarith
  have h1 : 0 < x - 1 := by linarith
  have h2 : 0 < x - 2 := by linarith
  have h : 0 ≤ x - 11 := by linarith
  have n0 : x ≠ 0 := h0.ne'
  have n1 : x - 1 ≠ 0 := h1.ne'
  have n2 : x - 2 ≠ 0 := h2.ne'
  have e : 22 / 9 * x⁻¹ ^ 2 - ((x - 1)⁻¹ - x⁻¹ + (x - 1)⁻¹ * (x - 2)⁻¹) = (4 * x ^ 2 - 48 * x + 44) / (9 * x ^ 2 * (x - 1) * (x - 2)) := by
    field_simp <;> ring
  have hd : 0 ≤ 22 / 9 * x⁻¹ ^ 2 - ((x - 1)⁻¹ - x⁻¹ + (x - 1)⁻¹ * (x - 2)⁻¹) := by
    rw [e]
    exact div_nonneg (by nlinarith [h, mul_nonneg h h]) (mul_nonneg (mul_nonneg (by positivity) h1.le) h2.le)
  linarith

lemma r21 (hx : 11 ≤ x) : (2 * x - 1) / (x - 1) ^ 2 ≤ 21 / 100 := by
  have h0 : 0 < x := by linarith
  have h1 : 0 < x - 1 := by linarith
  have h2 : 0 < x - 2 := by linarith
  have h : 0 ≤ x - 11 := by linarith
  have n0 : x ≠ 0 := h0.ne'
  have n1 : x - 1 ≠ 0 := h1.ne'
  have n2 : x - 2 ≠ 0 := h2.ne'
  have e : 21 / 100 - (2 * x - 1) / (x - 1) ^ 2 = (21 * x ^ 2 - 242 * x + 121) / (100 * (x - 1) ^ 2) := by
    field_simp <;> ring
  have hd : 0 ≤ 21 / 100 - (2 * x - 1) / (x - 1) ^ 2 := by
    rw [e]
    exact div_nonneg (by nlinarith [h, mul_nonneg h h]) (mul_nonneg (by norm_num) (sq_nonneg _))
  linarith

end Formalism.MainNotions.N.FrobeniusPowerSeries.NumericInequalities
