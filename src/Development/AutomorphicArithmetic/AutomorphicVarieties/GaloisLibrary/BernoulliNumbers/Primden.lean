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
import Mathlib.NumberTheory.Bernoulli
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

open Finset UpperTheory.V.Bern

theorem UpperTheory.V.Bern.b_primden :
    ∀ (k j : ℕ), j ≤ k → ∃ z : ℤ, (primorial (k + 1) : ℚ) * bernoulli j = z := by
  intro k j hjk
  have hdvd : ∀ p : ℕ, p.Prime → p ≤ k + 1 → p ∣ primorial (k + 1) := by
    intro p hp hpk
    exact Finset.dvd_prod_of_mem _ (Finset.mem_filter.2 ⟨Finset.mem_range.2 (by omega), hp⟩)
  rcases Nat.even_or_odd j with ⟨m, rfl⟩ | hodd
  · obtain ⟨z0, hz0⟩ := Bernoulli.vonStaudt_clausen m
    have h2 : m + m = 2 * m := by ring
    rw [h2]
    have hB : bernoulli (2 * m) = (z0 : ℚ) - ∑ p ∈ range (2 * m + 2) with Nat.Prime p ∧ p - 1 ∣ 2 * m, (1 : ℚ) / p := by
      rw [hz0]; ring
    refine ⟨(primorial (k + 1) : ℤ) * z0 - ∑ p ∈ range (2 * m + 2) with Nat.Prime p ∧ p - 1 ∣ 2 * m, ((primorial (k + 1) / p : ℕ) : ℤ), ?_⟩
    rw [Int.cast_sub, Int.cast_mul, Int.cast_sum]
    simp only [Int.cast_natCast]
    rw [hB, mul_sub, Finset.mul_sum]
    congr 1
    refine Finset.sum_congr rfl fun p hp => ?_
    rw [Finset.mem_filter, Finset.mem_range] at hp
    have hpd : p ∣ primorial (k + 1) := hdvd p hp.2.1 (by omega)
    rw [Nat.cast_div hpd (Nat.cast_ne_zero.2 hp.2.1.ne_zero)]
    ring
  · rcases Nat.lt_or_ge 1 j with h1 | h1
    · exact ⟨0, by rw [bernoulli_eq_zero_of_odd hodd h1]; simp⟩
    · have hj : j = 1 := by
        obtain ⟨r, rfl⟩ := hodd
        omega
      subst hj
      obtain ⟨t, ht⟩ := hdvd 2 Nat.prime_two (by omega)
      refine ⟨-(t : ℤ), ?_⟩
      rw [bernoulli_one, ht]
      push_cast
      ring
