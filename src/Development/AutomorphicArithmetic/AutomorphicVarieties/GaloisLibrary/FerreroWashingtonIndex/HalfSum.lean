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
import Mathlib.Topology.Sheaves.Init

open UpperTheory.V.FW

theorem UpperTheory.V.FW.halfSum :
    ∀ (α k : Type) [AddCommMonoid k] (σ : α → α) (H H' : Finset α) (g : α → k), (∀ x, σ (σ x) = x) → (∀ x, g (σ x) = g x) → (∀ x ∈ H, σ x ∉ H) → (∀ x ∈ H', σ x ∉ H') → (∀ x ∈ H, x ∈ H' ∨ σ x ∈ H') → (∀ x ∈ H', x ∈ H ∨ σ x ∈ H) → ∑ x ∈ H, g x = ∑ x ∈ H', g x := by
  classical
  intro α k _ σ H H' g hσ hg hH hH' hHH' hH'H
  refine Finset.sum_bij' (fun x _ => if x ∈ H' then x else σ x) (fun y _ => if y ∈ H then y else σ y)
    ?_ ?_ ?_ ?_ ?_
  · intro x hx
    by_cases h : x ∈ H'
    · simp [h]
    · simp only [h, if_false]
      exact (hHH' x hx).resolve_left h
  · intro y hy
    by_cases h : y ∈ H
    · simp [h]
    · simp only [h, if_false]
      exact (hH'H y hy).resolve_left h
  · intro x hx
    by_cases h : x ∈ H'
    · simp [h, hx]
    · simp [h, hH x hx, hσ]
  · intro y hy
    by_cases h : y ∈ H
    · simp [h, hy]
    · simp [h, hH' y hy, hσ]
  · intro x hx
    by_cases h : x ∈ H'
    · simp [h]
    · simp [h, hg]
