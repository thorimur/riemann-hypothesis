import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.CStarAlgebra.Classes
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

open Matrix

namespace GlobalTheory

theorem laurentMonomial_of_multiplicative :
    ∀ (n : ℕ) (χ : (Fin n → ℂ) → ℂ), χ 1 = 1 →
      (∀ s t : Fin n → ℂ, (∀ i, s i ≠ 0) → (∀ i, t i ≠ 0) → χ (s * t) = χ s * χ t) →
      (∀ i : Fin n, ∃ k : ℤ, ∀ t : ℂ, t ≠ 0 → χ (Pi.mulSingle i t) = t ^ k) →
      ∃ μ : Fin n → ℤ, ∀ d : Fin n → ℂ, (∀ i, d i ≠ 0) → χ d = ∏ i, d i ^ μ i := by
  intro n χ h1 hmul hk
  choose k hk using hk
  refine ⟨k, fun d hd => ?_⟩
  have hne : ∀ (s : Finset (Fin n)) (i : Fin n), (∏ j ∈ s, Pi.mulSingle j (d j)) i ≠ 0 := by
    intro s i
    rw [Finset.prod_apply]
    refine Finset.prod_ne_zero_iff.mpr fun j _ => ?_
    rw [Pi.mulSingle_apply]
    split_ifs with h
    · subst h; exact hd _
    · exact one_ne_zero
  have key : ∀ s : Finset (Fin n), χ (∏ i ∈ s, Pi.mulSingle i (d i)) = ∏ i ∈ s, d i ^ k i := by
    intro s
    refine Finset.induction_on s ?_ ?_
    · simpa using h1
    · intro a s ha ih
      rw [Finset.prod_insert ha, Finset.prod_insert ha, hmul _ _ ?_ (hne s), hk a (d a) (hd a), ih]
      intro i
      rw [Pi.mulSingle_apply]
      split_ifs with h
      · subst h; exact hd _
      · exact one_ne_zero
  have := key Finset.univ
  rwa [Finset.univ_prod_mulSingle] at this

end GlobalTheory
