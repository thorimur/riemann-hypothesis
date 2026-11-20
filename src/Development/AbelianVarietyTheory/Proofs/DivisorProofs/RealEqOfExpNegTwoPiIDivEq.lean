import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.Int.Star
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

namespace GlobalTheory

theorem exists_int_sub_eq_mul_of_exp_neg_two_pi_I_div_eq (x y : ℝ) (k : ℕ) (hk : 0 < k)
    (h : Complex.exp (-(2 * Real.pi * Complex.I) * (x : ℂ) / k) =
      Complex.exp (-(2 * Real.pi * Complex.I) * (y : ℂ) / k)) :
    ∃ n : ℤ, y - x = n * k := by
  obtain ⟨n, hn⟩ := Complex.exp_eq_exp_iff_exists_int.mp h
  refine ⟨n, ?_⟩
  have hk' : (k : ℂ) ≠ 0 := by exact_mod_cast hk.ne'
  have hpi : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := by
    simp [Real.pi_ne_zero, Complex.I_ne_zero]
  have : ((y - x : ℝ) : ℂ) = ((n * k : ℝ) : ℂ) := by
    push_cast
    field_simp at hn
    linear_combination hn
  exact_mod_cast this

theorem real_eq_of_exp_neg_two_pi_I_div_eq : ∀ x y : ℝ, (∀ k : ℕ, 0 < k →
    Complex.exp (-(2 * Real.pi * Complex.I) * (x : ℂ) / k) = Complex.exp (-(2 * Real.pi * Complex.I) * (y : ℂ) / k)) →
    x = y := by
  intro x y h
  obtain ⟨m, hm⟩ := exists_int_sub_eq_mul_of_exp_neg_two_pi_I_div_eq x y 1 one_pos (h 1 one_pos)
  simp only [Nat.cast_one, mul_one] at hm
  obtain ⟨n, hn⟩ := exists_int_sub_eq_mul_of_exp_neg_two_pi_I_div_eq x y (m.natAbs + 1) (Nat.succ_pos _)
    (h _ (Nat.succ_pos _))
  generalize hK : m.natAbs + 1 = K at hn
  have hmn : m = n * (K : ℤ) := by
    have : ((m : ℤ) : ℝ) = ((n * (K : ℤ) : ℤ) : ℝ) := by push_cast; rw [← hm, hn]
    exact_mod_cast this
  have hm0 : m = 0 := by
    by_contra hne
    have hn0 : n ≠ 0 := by
      rintro rfl
      exact hne (by simpa using hmn)
    have h1 : m.natAbs = n.natAbs * K := by
      rw [hmn, Int.natAbs_mul]; simp
    have h2 : 1 ≤ n.natAbs := Int.natAbs_pos.mpr hn0
    nlinarith
  have : y - x = 0 := by rw [hm, hm0]; simp
  linarith

end GlobalTheory
