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
import Mathlib.Topology.Separation.CompletelyRegular
import Mathlib.Topology.Sheaves.Init

open scoped BigOperators
open Matrix

namespace GlobalTheory

theorem exists_forall_ne_zero_of_countable_analytic :
    ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E] (U : Set E),
      IsOpen U → IsPreconnected U → U.Nonempty → ∀ (ι : Type) [Countable ι] (f : ι → E → ℂ),
      (∀ i, AnalyticOnNhd ℂ (f i) U) → (∀ i, ∃ x ∈ U, f i x ≠ 0) →
      ∃ x ∈ U, ∀ i, f i x ≠ 0 := by
  intro E _ _ _ U hU hc hne ι _ f hf hnz
  let S : ι → Set E := fun i => (U ∩ f i ⁻¹' ({0}ᶜ)) ∪ (closure U)ᶜ
  have hopen : ∀ i, IsOpen (S i) := fun i =>
    ((hf i).continuousOn.isOpen_inter_preimage hU isOpen_compl_singleton).union
      isClosed_closure.isOpen_compl
  have hdense : ∀ i, Dense (S i) := by
    intro i
    rw [dense_iff_inter_open]
    intro V hV hVne
    by_cases hVU : (V ∩ U).Nonempty
    · obtain ⟨z, hzV, hzU⟩ := hVU
      by_contra hcon
      have hzero : ∀ y ∈ V ∩ U, f i y = 0 := by
        intro y hy
        by_contra hy0
        exact hcon ⟨y, hy.1, Or.inl ⟨hy.2, hy0⟩⟩
      have hev : f i =ᶠ[nhds z] 0 := by
        filter_upwards [(hV.inter hU).mem_nhds ⟨hzV, hzU⟩] with y hy
        exact hzero y hy
      have hall := (hf i).eqOn_zero_of_preconnected_of_eventuallyEq_zero hc hzU hev
      obtain ⟨x, hxU, hx⟩ := hnz i
      exact hx (hall hxU)
    · obtain ⟨z, hzV⟩ := hVne
      refine ⟨z, hzV, Or.inr ?_⟩
      intro hz
      exact hVU (mem_closure_iff.1 hz V hV hzV)
  have hD : Dense (⋂ i, S i) := dense_iInter_of_isOpen hopen hdense
  obtain ⟨x, hxU, hx⟩ := hD.inter_open_nonempty U hU hne
  refine ⟨x, hxU, fun i => ?_⟩
  rcases Set.mem_iInter.1 hx i with h | h
  · exact h.2
  · exact absurd (subset_closure hxU) h

end GlobalTheory
