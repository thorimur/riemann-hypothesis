import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Altitude
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.PowerSeries.Substitution
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.SimpleRing.Principal
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

namespace GlobalTheory

open PowerSeries in

theorem powerSeries_eq_C_of_subst_eq_self (L : Type) [Field L] (y : PowerSeries L)
    (hy : PowerSeries.constantCoeff y = 0)
    (hu : ∀ k : ℕ, 0 < k → (PowerSeries.coeff 1 y) ^ k ≠ 1) (a : PowerSeries L)
    (ha : (PowerSeries.subst y a : PowerSeries L) = a) :
    a = PowerSeries.C (PowerSeries.constantCoeff a) := by
  classical
  obtain ⟨z, rfl⟩ : X ∣ y := by rwa [PowerSeries.X_dvd_iff]
  have hs : HasSubst (X * z) := HasSubst.of_constantCoeff_zero' hy
  have hu1 : coeff 1 (X * z) = constantCoeff z := by
    rw [coeff_succ_X_mul, coeff_zero_eq_constantCoeff_apply]
  rw [hu1] at hu

  have hc : ∀ n, coeff n (a.subst (X * z)) =
      ∑ d ∈ Finset.range (n + 1), coeff d a * coeff (n - d) (z ^ d) := by
    intro n
    rw [coeff_subst' hs, finsum_eq_sum_of_support_subset (s := Finset.range (n + 1))]
    · refine Finset.sum_congr rfl fun d hd => ?_
      rw [mul_pow, coeff_X_pow_mul', if_pos (Nat.lt_succ_iff.mp (Finset.mem_range.mp hd)),
        smul_eq_mul]
    · intro d hd
      rw [Function.mem_support] at hd
      rw [Finset.coe_range, Set.mem_Iio]
      by_contra h
      apply hd
      rw [mul_pow, coeff_X_pow_mul', if_neg (by omega), smul_zero]

  have main : ∀ k, 0 < k → coeff k a = 0 := by
    intro k
    induction k using Nat.strong_induction_on with
    | _ k ih =>
      intro hk
      have h1 := hc k
      rw [ha, Finset.sum_range_succ, Finset.sum_eq_zero, zero_add, Nat.sub_self,
        coeff_zero_eq_constantCoeff_apply, map_pow] at h1
      · have h2 : coeff k a * (1 - constantCoeff z ^ k) = 0 := by
          rw [mul_sub, mul_one, ← h1, sub_self]
        rcases mul_eq_zero.mp h2 with h | h
        · exact h
        · exact absurd (sub_eq_zero.mp h).symm (hu k hk)
      · intro d hd
        rcases Nat.eq_zero_or_pos d with rfl | hd0
        · simp [coeff_one, hk.ne']
        · rw [ih d (Finset.mem_range.mp hd) hd0, zero_mul]
  ext n
  rcases n with _ | n
  · simp
  · rw [coeff_C, if_neg (Nat.succ_ne_zero n)]
    exact main (n + 1) (Nat.succ_pos n)

end GlobalTheory
