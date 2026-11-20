import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.CStarAlgebra.Classes
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
import Mathlib.Topology.Sheaves.Init

namespace GlobalTheory.EqOneOfPowerClose

open Finset

theorem eq_one_of_pow_close {u : ℂ} (h : ∀ n : ℕ, ‖u ^ n - (1 : ℂ)‖ < (1 / 2 : ℝ)) :
    u = (1 : ℂ) := by
  have key : ∀ n : ℕ, (n : ℝ) * ‖u - 1‖ ≤ 1 := by
    intro n
    have h1 : ‖∑ k ∈ range n, (u ^ k - 1)‖ ≤ (n : ℝ) / 2 := by
      calc ‖∑ k ∈ range n, (u ^ k - 1)‖ ≤ ∑ k ∈ range n, ‖u ^ k - 1‖ := norm_sum_le _ _
        _ ≤ ∑ _k ∈ range n, (1 / 2 : ℝ) := sum_le_sum fun k _ => (h k).le
        _ = (n : ℝ) / 2 := by simp; ring
    have h2 : (n : ℂ) = ∑ k ∈ range n, u ^ k - ∑ k ∈ range n, (u ^ k - 1) := by
      rw [sum_sub_distrib]; simp
    have h3 : (n : ℝ) ≤ ‖∑ k ∈ range n, u ^ k‖ + ‖∑ k ∈ range n, (u ^ k - 1)‖ := by
      have := norm_sub_le (∑ k ∈ range n, u ^ k) (∑ k ∈ range n, (u ^ k - 1))
      rw [← h2, Complex.norm_natCast] at this
      exact this
    have h4 : ‖∑ k ∈ range n, u ^ k‖ * ‖u - 1‖ < 1 / 2 := by
      rw [← norm_mul, geom_sum_mul]; exact h n
    have h5 : (n : ℝ) / 2 ≤ ‖∑ k ∈ range n, u ^ k‖ := by linarith
    have h6 := mul_le_mul_of_nonneg_right h5 (norm_nonneg (u - 1))
    linarith
  by_contra hne
  have hpos : 0 < ‖u - 1‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hne)
  obtain ⟨n, hn⟩ := exists_nat_gt (1 / ‖u - 1‖)
  rw [div_lt_iff₀ hpos] at hn
  linarith [key n]

end GlobalTheory.EqOneOfPowerClose
