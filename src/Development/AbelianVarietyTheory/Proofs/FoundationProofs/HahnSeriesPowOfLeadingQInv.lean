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
import Mathlib.RingTheory.HahnSeries.Multiplication
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
open scoped MatrixGroups
open GlobalTheory.KZ

namespace GlobalTheory

theorem hahn_pow_neg_one_lead {R : Type} [CommRing R] (x : HahnSeries ℚ R)
    (h1 : x.coeff (-1) = 1) (hlt : ∀ r : ℚ, r < -1 → x.coeff r = 0) :
    ∀ m : ℕ, (x ^ m).coeff (-(m : ℚ)) = 1 ∧ ∀ r : ℚ, r < -(m : ℚ) → (x ^ m).coeff r = 0 := by
  intro m
  rcases subsingleton_or_nontrivial R with hR | hR
  · exact ⟨Subsingleton.elim _ _, fun r _ => Subsingleton.elim _ _⟩
  have hx0 : x ≠ 0 := by
    intro h; rw [h] at h1; simp at h1
  have hxo : x.order = -1 := by
    refine le_antisymm (HahnSeries.order_le_of_coeff_ne_zero (by rw [h1]; exact one_ne_zero)) ?_
    by_contra hc
    push_neg at hc
    exact hx0 (HahnSeries.coeff_order_eq_zero.mp (hlt _ hc))
  have hxl : x.leadingCoeff = 1 := by
    rw [HahnSeries.leadingCoeff_eq, hxo, h1]
  have key : ∀ n : ℕ, (x ^ n).order = -(n : ℚ) ∧ (x ^ n).leadingCoeff = 1 := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      have hne : (x ^ n).leadingCoeff * x.leadingCoeff ≠ 0 := by
        rw [ih.2, hxl, one_mul]; exact one_ne_zero
      rw [pow_succ, HahnSeries.order_mul_of_ne_zero hne, HahnSeries.leadingCoeff_mul_of_ne_zero hne,
        ih.1, ih.2, hxo, hxl]
      constructor
      · push_cast; ring
      · simp
  obtain ⟨ho, hl⟩ := key m
  refine ⟨?_, fun r hr => ?_⟩
  · rw [← ho, ← HahnSeries.leadingCoeff_eq, hl]
  · exact HahnSeries.coeff_eq_zero_of_lt_order (by rw [ho]; exact hr)

end GlobalTheory
