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

namespace GlobalTheory.NormSumLt

universe u_1

theorem norm_sum_lt {K : Type u_1} [NormedField K] [IsUltrametricDist K] (s : Finset ℕ) (f : ℕ → K)
    {r : ℝ} (hr : (0 : ℝ) < r) (h : ∀ i ∈ s, ‖f i‖ < r) : ‖∑ i ∈ s, f i‖ < r := by
  induction s using Finset.induction_on with
  | empty => simpa using hr
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    have h1 : ‖f a‖ < r := h a (Finset.mem_insert_self a s)
    have h2 : ‖∑ i ∈ s, f i‖ < r := ih (fun i hi => h i (Finset.mem_insert_of_mem hi))
    exact lt_of_le_of_lt (IsUltrametricDist.norm_add_le_max _ _) (max_lt h1 h2)

theorem main : ∀ {K : Type u_1} [inst : NormedField K] [IsUltrametricDist K] (s : Finset ℕ) (f : ℕ → K) {r : ℝ}, (0 : ℝ) < r → (∀ i ∈ s, ‖f i‖ < r) → ‖∑ i ∈ s, f i‖ < r :=
  by
  intro K _ _ s f r hr h
  exact norm_sum_lt s f hr h

end GlobalTheory.NormSumLt
