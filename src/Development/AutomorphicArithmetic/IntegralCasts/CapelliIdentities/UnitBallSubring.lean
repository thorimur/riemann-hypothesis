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

private def unitBallSubring (K : Type) [NormedField K] [IsUltrametricDist K] : Subring K where
  carrier := {x | ‖x‖ ≤ 1}
  mul_mem' := by
    intro a b ha hb
    simp only [Set.mem_setOf_eq] at *
    rw [norm_mul]
    exact mul_le_one₀ ha (norm_nonneg _) hb
  one_mem' := by simp
  add_mem' := by
    intro a b ha hb
    simp only [Set.mem_setOf_eq] at *
    exact (IsUltrametricDist.norm_add_le_max a b).trans (max_le ha hb)
  zero_mem' := by simp
  neg_mem' := by
    intro a ha
    simpa using ha

theorem UpperTheory.Reformulated.B.Qh18.rootb :
    ∀ {K : Type} [inst : NormedField K] [IsUltrametricDist K] (l m : ℕ),
    Nat.Prime l → l ≠ (2 : ℕ) → ∀ (z : K), z ^ l ^ m = (1 : K) → ‖z - (1 : K)‖ ^ l ^ m ≤ ‖(↑l : K)‖ := by
  intro K _ _ l m hl _ z hz
  have hN : l ^ m ≠ 0 := pow_ne_zero _ hl.ne_zero
  have hz1 : ‖z‖ = 1 := by
    have h := congrArg norm hz
    rw [norm_pow, norm_one] at h
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) hN).1 h
  have hzS : z ∈ unitBallSubring K := hz1.le
  have hx : z - 1 ∈ unitBallSubring K := sub_mem hzS (one_mem _)
  obtain ⟨r, hr⟩ := exists_add_pow_prime_pow_eq hl (⟨z - 1, hx⟩ : unitBallSubring K) 1 m
  have hr' := congrArg (Subtype.val) hr
  push_cast at hr'
  have hrn : ‖(r : K)‖ ≤ 1 := r.2
  have hxn : ‖z - 1‖ ≤ 1 := hx
  rw [sub_add_cancel, hz] at hr'
  have e : (z - 1) ^ l ^ m = -((l : K) * ((z - 1) * (r : K))) := by
    simp only [one_pow, mul_one] at hr'
    linear_combination (-1 : K) * hr'
  rw [← norm_pow, e, norm_neg, norm_mul, norm_mul]
  exact mul_le_of_le_one_right (norm_nonneg _) (mul_le_one₀ hxn (norm_nonneg _) hrn)
