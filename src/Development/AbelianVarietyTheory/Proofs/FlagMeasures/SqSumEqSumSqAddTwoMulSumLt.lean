import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Ring.Star
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

open Matrix Finset Real

namespace GlobalTheory

open Matrix Finset Real in

theorem _root_.GlobalTheory.sq_sum_eq_sum_sq_add_two_mul_sum_lt (a : ℕ) (j : Fin a → ℤ) :
    (∑ i, j i) ^ 2 = ∑ i, j i ^ 2 + 2 * ∑ i, ∑ k, if i < k then j i * j k else 0 := by
  have h : ∀ i k : Fin a, j i * j k = (if i < k then j i * j k else 0) +
      (if k < i then j k * j i else 0) + (if i = k then j i ^ 2 else 0) := by
    intro i k
    rcases lt_trichotomy i k with hik | hik | hik
    · simp [hik, hik.ne, not_lt.mpr hik.le]
    · subst hik; simp [sq]
    · simp [hik, hik.ne', not_lt.mpr hik.le, mul_comm]
  calc (∑ i, j i) ^ 2 = ∑ i, ∑ k, j i * j k := by rw [sq, Finset.sum_mul_sum]
    _ = ∑ i, ∑ k, ((if i < k then j i * j k else 0) + (if k < i then j k * j i else 0) +
          (if i = k then j i ^ 2 else 0)) :=
        Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => h i k
    _ = _ := by
        simp only [Finset.sum_add_distrib]
        rw [Finset.sum_comm (f := fun i k => if k < i then j k * j i else 0)]
        simp only [Finset.sum_ite_eq, Finset.mem_univ, if_true]
        ring

open Matrix Finset Real in

theorem _root_.GlobalTheory.dim_unipotent_radical_identities :
    ∀ (a : ℕ) (j : Fin a → ℤ) (n : ℤ), let J := ∑ i, j i; let n₀ := n - 2 * J; let dimN := 4 * (∑ i, ∑ k, if i < k then j i * j k else 0) + 2 * J * n₀ + ∑ i, j i ^ 2; dimN = 2 * J ^ 2 - ∑ i, j i ^ 2 + 2 * J * n₀ ∧ n ^ 2 = n₀ ^ 2 + 2 * ∑ i, j i ^ 2 + 2 * dimN ∧ dimN ≤ 2 * J * n := by
  intro a j n
  dsimp only
  have key := _root_.GlobalTheory.sq_sum_eq_sum_sq_add_two_mul_sum_lt a j
  have hQ : 0 ≤ ∑ i, j i ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg (j i)
  generalize (∑ i, ∑ k, if i < k then j i * j k else 0) = S at key ⊢
  generalize (∑ i, j i ^ 2) = Q at key hQ ⊢
  generalize (∑ i, j i) = J at key ⊢
  refine ⟨by linear_combination (-2) * key, by linear_combination 4 * key, ?_⟩
  nlinarith [key, sq_nonneg J, hQ]

end GlobalTheory
