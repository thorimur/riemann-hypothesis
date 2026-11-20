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
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop

namespace GlobalTheory.ClosedSubgroupCriterion

theorem main : ∀ {n j : ℕ} (a : Fin n → ℤ), Antitone a → (∀ (i : Fin n), a i = (0 : ℤ) ∨ a i = (1 : ℤ)) →
    Finset.card {i : Fin n | a i = (1 : ℤ)} = j → ∀ (i : Fin n), a i = (1 : ℤ) ↔ (↑i : ℕ) < j := by
  intro n j a ha h01 hj i
  constructor
  · intro hi
    by_contra hlt
    push_neg at hlt
    have hsub : Finset.Iic i ⊆ ({k : Fin n | a k = (1:ℤ)} : Finset (Fin n)) := by
      intro k hk
      rw [Finset.mem_Iic] at hk
      have := ha hk
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      rcases h01 k with h | h
      · rw [h, hi] at this; norm_num at this
      · exact h
    have := Finset.card_le_card hsub
    rw [Fin.card_Iic, hj] at this
    omega
  · intro hi
    rcases h01 i with h | h
    · exfalso
      have hsub : ({k : Fin n | a k = (1:ℤ)} : Finset (Fin n)) ⊆ Finset.Iio i := by
        intro k hk
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk
        rw [Finset.mem_Iio]
        by_contra hle
        push_neg at hle
        have := ha hle
        rw [h, hk] at this; norm_num at this
      have := Finset.card_le_card hsub
      rw [Fin.card_Iio, hj] at this
      omega
    · exact h

end GlobalTheory.ClosedSubgroupCriterion
