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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
open NumberField

namespace GlobalTheory

theorem finsum_padicValNat_mul_log_eq_log :
    ∀ m : ℕ, m ≠ 0 → (Function.support fun p : ℕ => if p.Prime then (padicValNat p m : ℝ) * Real.log p else 0).Finite ∧ ∑ᶠ p : ℕ, (if p.Prime then (padicValNat p m : ℝ) * Real.log p else 0) = Real.log m := by
  intro m hm
  have hsupp : (Function.support fun p : ℕ => if p.Prime then (padicValNat p m : ℝ) * Real.log p else 0) ⊆ (m.primeFactors : Set ℕ) := by
    intro p hp
    simp only [Function.mem_support, ne_eq] at hp
    by_cases hpp : p.Prime
    · rw [if_pos hpp] at hp
      have h0 : padicValNat p m ≠ 0 := by
        intro h; apply hp; simp [h]
      have hdvd : p ∣ m := by
        by_contra hnd
        exact h0 (padicValNat.eq_zero_of_not_dvd hnd)
      simp only [Finset.mem_coe, Nat.mem_primeFactors]
      exact ⟨hpp, hdvd, hm⟩
    · exact absurd (if_neg hpp) hp
  refine ⟨(Finset.finite_toSet _).subset hsupp, ?_⟩
  rw [finsum_eq_sum_of_support_subset _ hsupp, Real.log_nat_eq_sum_factorization, Finsupp.sum,
    Nat.support_factorization]
  refine Finset.sum_congr rfl fun p hp => ?_
  have hpp : p.Prime := Nat.prime_of_mem_primeFactors hp
  rw [if_pos hpp, Nat.factorization_def m hpp]

end GlobalTheory
