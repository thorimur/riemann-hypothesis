import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.ExponentialBounds
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
import Mathlib.Topology.Sheaves.Presheaf

theorem UpperTheory.sum_log_primeFactors_mul_two_add_logb_le :
    ∀ (Q : ℕ) (y : ℝ), Q ≠ 0 → 1 ≤ y → Real.log Q ≤ y →
      (∑ p ∈ Q.primeFactors, Real.log (p : ℝ)) * (2 + Real.logb 2 Q) ≤ 11 * y ^ 4 := by
  intro Q y hQ hy hlog
  have hQ1 : (1 : ℝ) ≤ Q := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hQ
  have hl0 : 0 ≤ Real.log Q := Real.log_nonneg hQ1
  have hpos : ∀ p ∈ Q.primeFactors, (0 : ℝ) < p := fun p hp => by
    exact_mod_cast (Nat.prime_of_mem_primeFactors hp).pos
  have h1 : (∑ p ∈ Q.primeFactors, Real.log (p : ℝ)) ≤ y := by
    rw [← Real.log_prod (fun p hp => (hpos p hp).ne')]
    refine le_trans (Real.log_le_log (Finset.prod_pos hpos) ?_) hlog
    have := Nat.le_of_dvd (Nat.pos_of_ne_zero hQ) (Nat.prod_primeFactors_dvd Q)
    rw [← Nat.cast_prod]
    exact Nat.cast_le.mpr this
  have h2 : Real.logb 2 Q ≤ 2 * y := by
    have hl2 : (1 / 2 : ℝ) < Real.log 2 := by
      have := Real.log_two_gt_d9
      linarith
    rw [Real.logb, div_le_iff₀ (by linarith)]
    nlinarith
  have h3 : 0 ≤ Real.logb 2 Q := Real.logb_nonneg (by norm_num) hQ1
  have h4 : y ^ 2 ≤ y ^ 4 := pow_le_pow_right₀ hy (by norm_num)
  calc (∑ p ∈ Q.primeFactors, Real.log (p : ℝ)) * (2 + Real.logb 2 Q)
      ≤ y * (2 + Real.logb 2 Q) := mul_le_mul_of_nonneg_right h1 (by linarith)
    _ ≤ y * (4 * y) := mul_le_mul_of_nonneg_left (by linarith) (by linarith)
    _ ≤ 11 * y ^ 4 := by nlinarith
