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

namespace GlobalTheory.NonarchimedeanSumBound

theorem sum_le_of_nonarch {K : Type} [Field K] (w : AbsoluteValue K ℝ)
    (hw : IsNonarchimedean (⇑w : K → ℝ)) {ι : Type} (s : Finset ι) (f : ι → K) {c : ℝ}
    (hc : (0 : ℝ) ≤ c) (h : ∀ i ∈ s, (w : K → ℝ) (f i) ≤ c) :
    (w : K → ℝ) (∑ i ∈ s, f i) ≤ c := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using hc
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact (hw _ _).trans (max_le (h a (Finset.mem_insert_self a s))
      (ih fun i hi => h i (Finset.mem_insert_of_mem hi)))

theorem main : ∀ {K : Type} [inst : Field K] (w : AbsoluteValue K ℝ), IsNonarchimedean (⇑w : K → ℝ) → ∀ {ι : Type} (s : Finset ι) (f : ι → K) {c : ℝ}, (0 : ℝ) ≤ c → (∀ i ∈ s, (w : K → ℝ) (f i) ≤ c) → (w : K → ℝ) (∑ i ∈ s, f i) ≤ c :=
  fun w hw _ s f _ hc h => sum_le_of_nonarch w hw s f hc h

end GlobalTheory.NonarchimedeanSumBound
