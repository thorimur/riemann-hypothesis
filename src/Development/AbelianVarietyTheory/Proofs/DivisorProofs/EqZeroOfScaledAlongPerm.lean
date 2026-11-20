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

namespace GlobalTheory

theorem eq_zero_of_scaled_along_perm : ∀ (ι : Type) [Fintype ι] (φ : Equiv.Perm ι) (p : ℕ) (h : ι → ℤ), 2 ≤ p → (∀ σ, h (φ σ) = p * h σ) → ∀ σ, h σ = 0 := by
  intro ι _ φ p h hp hφ σ
  have key : ∀ k : ℕ, h ((φ ^ k) σ) = (p : ℤ) ^ k * h σ := by
    intro k
    induction k with
    | zero => simp
    | succ k ih => rw [pow_succ', Equiv.Perm.mul_apply, hφ, ih]; ring
  have hpos : 0 < orderOf φ := orderOf_pos φ
  have hk := key (orderOf φ)
  rw [pow_orderOf_eq_one, Equiv.Perm.one_apply] at hk
  have hp1 : (1 : ℤ) < p := by exact_mod_cast (show 1 < p by omega)
  have hp' : (1 : ℤ) < (p : ℤ) ^ (orderOf φ) := one_lt_pow₀ hp1 hpos.ne'
  have hz : ((p : ℤ) ^ (orderOf φ) - 1) * h σ = 0 := by linear_combination -hk
  rcases mul_eq_zero.mp hz with h1 | h1
  · linarith
  · exact h1

end GlobalTheory
