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
open GlobalTheory.AlmostEt
open scoped NNReal

namespace GlobalTheory.AlmostEt

theorem valuation_nnreal_natCast_le_one {L : Type} [Field L] (v : Valuation L ℝ≥0) (n : ℕ) : v (n : L) ≤ 1 := by
  induction n with
  | zero => simp
  | succ k ih =>
    push_cast
    exact le_trans (v.map_add _ _) (max_le ih (by simp))

theorem valuation_nnreal_intCast_le_one {L : Type} [Field L] (v : Valuation L ℝ≥0) (z : ℤ) : v (z : L) ≤ 1 := by
  cases z with
  | ofNat n => simpa using valuation_nnreal_natCast_le_one v n
  | negSucc n =>
    rw [Int.cast_negSucc, Valuation.map_neg]
    exact_mod_cast valuation_nnreal_natCast_le_one v (n + 1)

theorem natCast_eq_one_of_coprime :
    ∀ (L : Type) [Field L] (v : Valuation L ℝ≥0) (p l : ℕ), v (p : L) < 1 → Nat.Coprime l p → v (l : L) = 1 := by
  intro L _ v p l hp hlp
  refine le_antisymm (valuation_nnreal_natCast_le_one v l) ?_
  by_contra hlt
  push_neg at hlt
  have hb : ((Nat.gcd l p : ℕ) : ℤ) = (l : ℤ) * Nat.gcdA l p + (p : ℤ) * Nat.gcdB l p := Nat.gcd_eq_gcd_ab l p
  rw [hlp, Nat.cast_one] at hb
  have hL : (1 : L) = (l : L) * (Nat.gcdA l p : L) + (p : L) * (Nat.gcdB l p : L) := by
    have := congrArg (fun z : ℤ => (z : L)) hb
    push_cast at this
    exact this
  have h1 : v (1 : L) < 1 := by
    rw [hL]
    refine lt_of_le_of_lt (v.map_add _ _) (max_lt ?_ ?_)
    · rw [v.map_mul]
      exact lt_of_le_of_lt (mul_le_of_le_one_right (by positivity) (valuation_nnreal_intCast_le_one v (Nat.gcdA l p))) hlt
    · rw [v.map_mul]
      exact lt_of_le_of_lt (mul_le_of_le_one_right (by positivity) (valuation_nnreal_intCast_le_one v (Nat.gcdB l p))) hp
  simp at h1

end GlobalTheory.AlmostEt
