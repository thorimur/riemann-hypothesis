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

namespace GlobalTheory.VSubArith

theorem sq_le_two_pow_add_one (v : ℕ) : v * v ≤ 2 ^ v + 1 := by
  have key : ∀ k : ℕ, (k + 4) * (k + 4) ≤ 2 ^ (k + 4) ∧ 2 * (k + 4) + 1 ≤ 2 ^ (k + 4) := by
    intro k
    induction k with
    | zero => norm_num
    | succ k ih =>
      obtain ⟨h1, h2⟩ := ih
      rw [show k + 1 + 4 = (k + 4) + 1 by ring, pow_succ]
      constructor <;> nlinarith
  rcases Nat.lt_or_ge v 4 with h | h
  · interval_cases v <;> norm_num
  · obtain ⟨k, rfl⟩ : ∃ k, v = k + 4 := ⟨v - 4, by omega⟩
    exact le_trans (key k).1 (Nat.le_succ _)

theorem two_mul_le_sq_add_sq (v L : ℕ) : 2 * (v * L) ≤ v * v + L * L := by
  have h : (2 * (v * L) : ℤ) ≤ v * v + L * L := by nlinarith [sq_nonneg ((v : ℤ) - L)]
  exact_mod_cast h

theorem add_mul_le_of_pow_le : ∀ (p L m : ℕ), 2 ≤ p → ∃ M0 : ℕ, ∀ n v : ℕ, M0 ≤ n → p ^ v ≤ n → (v + m) * L ≤ n := by
  intro p L m hp
  refine ⟨L * L + 2 * m * L + 1, ?_⟩
  intro n v hn hpv
  have h2 : 2 ^ v ≤ p ^ v := Nat.pow_le_pow_left hp v
  have hsq := sq_le_two_pow_add_one v
  have hag := two_mul_le_sq_add_sq v L
  have hx : 2 * ((v + m) * L) ≤ n + n := by nlinarith
  linarith

end GlobalTheory.VSubArith
