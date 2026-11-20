import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Derangements.Finite
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
open Polynomial Classical GlobalTheory.BadShare

namespace GlobalTheory.BadShare

theorem two_mul_numDerangements_succ_le (n : ℕ) :
    2 * numDerangements (n + 1) ≤ (n + 1).factorial := by
  induction n using Nat.twoStepInduction with
  | zero => simp
  | one => simp [numDerangements]
  | more n h1 h2 =>
    have e : numDerangements (n + 2 + 1)
        = (n + 1 + 1) * (numDerangements (n + 1) + numDerangements (n + 1 + 1)) :=
      numDerangements_add_two (n + 1)
    have f1 : (n + 2 + 1).factorial = (n + 2 + 1) * (n + 1 + 1).factorial :=
      Nat.factorial_succ _
    have f2 : (n + 1 + 1).factorial = (n + 1 + 1) * (n + 1).factorial :=
      Nat.factorial_succ _
    rw [e, f1]
    have := Nat.mul_le_mul_left (n + 1 + 1) (Nat.add_le_add h1 h2)
    nlinarith

theorem factorial_le_two_mul_card_perm_fixed :
    ∀ (α : Type) [Fintype α] [DecidableEq α], Nonempty α →
      (Fintype.card α).factorial ≤
        2 * (Finset.univ.filter fun σ : Equiv.Perm α => ∃ i, σ i = i).card := by
  intro α _ _ hne
  have hsum := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Equiv.Perm α)))
    (fun σ : Equiv.Perm α => ∃ i, σ i = i)
  rw [Finset.card_univ, Fintype.card_perm] at hsum
  have hd : (Finset.univ.filter fun σ : Equiv.Perm α => ¬ ∃ i, σ i = i).card
      = numDerangements (Fintype.card α) := by
    rw [← card_derangements_eq_numDerangements α, ← Fintype.card_subtype]
    refine Fintype.card_congr (Equiv.subtypeEquivRight fun σ => ?_)
    simp [derangements]
  obtain ⟨n, hn⟩ : ∃ n, Fintype.card α = n + 1 :=
    Nat.exists_eq_succ_of_ne_zero Fintype.card_ne_zero
  have h := two_mul_numDerangements_succ_le n
  rw [← hn] at h
  omega

end GlobalTheory.BadShare
