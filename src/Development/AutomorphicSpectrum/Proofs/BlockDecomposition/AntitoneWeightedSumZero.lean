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
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop

namespace GlobalTheory.CompanionTheory.Tempered

theorem weighted_antitone_eq_zero_of_tails_nonneg :
    ∀ (h : ℕ) (d e : Fin h → ℝ), (∀ i, 0 < d i) → Antitone e → ∑ i, d i * e i = 0 →
      (∀ j : Fin h, 0 ≤ ∑ i ∈ Finset.univ.filter (fun i => j ≤ i), d i * e i) →
      ∀ i, e i = 0 := by
  intro h d e hd he hsum htail
  have hnn : ∀ i, 0 ≤ e i := by
    intro i
    by_contra hneg
    rw [not_le] at hneg
    have hlt : ∑ k ∈ Finset.univ.filter (fun k => i ≤ k), d k * e k < 0 := by
      apply Finset.sum_neg
      · intro k hk
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk
        exact mul_neg_of_pos_of_neg (hd k) (lt_of_le_of_lt (he hk) hneg)
      · exact ⟨i, by simp⟩
    linarith [htail i]
  have hz := (Finset.sum_eq_zero_iff_of_nonneg fun k _ => mul_nonneg (hd k).le (hnn k)).1 hsum
  intro i
  rcases mul_eq_zero.1 (hz i (Finset.mem_univ i)) with h1 | h1
  · exact absurd h1 (hd i).ne'
  · exact h1

end GlobalTheory.CompanionTheory.Tempered
