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

namespace KStar.Choice

structure RootData (S L : Finset ℕ) (ν o : ℕ → ℕ) : Prop where
  prime_small : ∀ l ∈ S, l.Prime
  nu_two : 0 < ν 2
  one_lt : ∀ l, l.Prime → ν l = 0 → 1 < o l
  unramified : ∀ l, l.Prime → l ≠ 2 → l ∉ S → l ∉ L → ν l = 0 ∧ o l = l - 1
  large : ∀ l ∈ L, ν l = 0 ∧ (l - 1) / 2 ≤ o l
  small : ∀ l ∈ S, o l ∣ l - 1

example : RootData {2} ∅ (fun l => if l = 2 then 1 else 0) (fun l => l - 1) where
  prime_small := by simp [Nat.prime_two]
  nu_two := by simp
  one_lt := fun l hl h => by
    have h2 : l ≠ 2 := by rintro rfl; simp at h
    have := hl.two_le; omega
  unramified := fun l _ h _ _ => by simp [h]
  large := by simp
  small := by simp

end KStar.Choice
