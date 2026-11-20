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
import Mathlib.RingTheory.Nilpotent.Exp
import Mathlib.RingTheory.PiTensorProduct
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

namespace GlobalTheory

open Finset

theorem eq_zero_of_isNilpotent_of_exp_eq_one {A : Type} [Ring A] [Algebra ℚ A] {m : A}
    (hm : IsNilpotent m) (h : IsNilpotent.exp m = 1) : m = 0 := by
  obtain ⟨k, hk⟩ := hm
  have hk2 : m ^ (k + 2) = 0 := pow_eq_zero_of_le (by omega) hk
  let v : A := ∑ i ∈ range k, (((i + 2).factorial : ℚ)⁻¹) • m ^ i
  let w : A := ∑ i ∈ range (k + 1), (((i + 1).factorial : ℚ)⁻¹) • m ^ i
  have hw : w = 1 + m * v := by
    simp only [w, v]
    rw [sum_range_succ', mul_sum, add_comm]
    congr 1
    · simp
    · refine sum_congr rfl fun i _ => ?_
      rw [mul_smul_comm, ← pow_succ']
  have hcomm : Commute m v :=
    Commute.sum_right _ _ _ fun i _ => ((Commute.refl m).pow_right i).smul_right _
  have hnil : IsNilpotent (m * v) := by
    first
      | exact hcomm.isNilpotent_mul_right ⟨k, hk⟩
      | exact hcomm.symm.isNilpotent_mul_left ⟨k, hk⟩
      | exact hcomm.isNilpotent_mul_left ⟨k, hk⟩
  have hunit : IsUnit w := hw ▸ hnil.isUnit_one_add
  have hmw : m * w = 0 := by
    rw [IsNilpotent.exp_eq_sum hk2, sum_range_succ'] at h
    simp only [pow_zero, Nat.factorial_zero, Nat.cast_one, inv_one, one_smul,
      add_eq_right] at h
    rw [← h]
    simp only [w]
    rw [mul_sum]
    refine sum_congr rfl fun i _ => ?_
    rw [mul_smul_comm, ← pow_succ']

  exact hunit.mul_left_eq_zero.mp hmw

theorem exp_injective_of_commute : ∀ (A : Type) [Ring A] [Algebra ℚ A] (a b : A), Commute a b →
    IsNilpotent a → IsNilpotent b → IsNilpotent.exp a = IsNilpotent.exp b → a = b := by
  intro A _ _ a b hab ha hb h
  have hm : IsNilpotent (a - b) := hab.isNilpotent_sub ha hb
  have hc : Commute (a - b) b := (hab.sub_left (Commute.refl b))
  have h1 : IsNilpotent.exp (a - b) * IsNilpotent.exp b = 1 * IsNilpotent.exp b := by
    rw [← IsNilpotent.exp_add_of_commute hc hm hb, sub_add_cancel, h, one_mul]
  have h2 : IsNilpotent.exp (a - b) = 1 :=
    (IsNilpotent.isUnit_exp hb).mul_right_cancel h1
  exact sub_eq_zero.mp (eq_zero_of_isNilpotent_of_exp_eq_one hm h2)

end GlobalTheory
