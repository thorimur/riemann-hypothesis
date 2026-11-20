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
import Mathlib.Order.CompletePartialOrder
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
open MeasureTheory Filter Topology
open scoped ENNReal

namespace GlobalTheory.CompanionTheory.MeasureTails

theorem tendsto_setLIntegral_diff_compactCovering
    {α : Type} [TopologicalSpace α] [MeasurableSpace α] [BorelSpace α] [T2Space α]
    [SigmaCompactSpace α] (μ : Measure α) (F : Set α) (h : α → ℝ≥0∞)
    (hfin : ∫⁻ x in F, h x ∂μ < ⊤) :
    Tendsto (fun k : ℕ => ∫⁻ x in F \ compactCovering α k, h x ∂μ) atTop (𝓝 0) := by
  set m : Measure α := (μ.restrict F).withDensity h with hm
  have hmeas : ∀ k : ℕ, MeasurableSet (compactCovering α k)ᶜ := fun k =>
    ((isCompact_compactCovering α k).isClosed.measurableSet).compl
  have hrew : ∀ k : ℕ, ∫⁻ x in F \ compactCovering α k, h x ∂μ = m (compactCovering α k)ᶜ := by
    intro k
    rw [hm, withDensity_apply h (hmeas k), Measure.restrict_restrict (hmeas k), Set.diff_eq,
      Set.inter_comm]
  have huniv : m Set.univ < ⊤ := by
    rw [hm, withDensity_apply h MeasurableSet.univ, Measure.restrict_univ]
    exact hfin
  have hanti : Antitone (fun k : ℕ => (compactCovering α k)ᶜ) := fun i j hij =>
    Set.compl_subset_compl.mpr (compactCovering_subset α hij)
  have hinter : ⋂ k : ℕ, (compactCovering α k)ᶜ = ∅ := by
    rw [← Set.compl_iUnion, iUnion_compactCovering, Set.compl_univ]
  have hne : ∃ k : ℕ, m (compactCovering α k)ᶜ ≠ ⊤ :=
    ⟨0, ne_top_of_le_ne_top huniv.ne (measure_mono (Set.subset_univ _))⟩
  have key := tendsto_measure_iInter_atTop (μ := m)
    (fun k => (hmeas k).nullMeasurableSet) hanti hne
  rw [hinter, measure_empty] at key
  simp only [hrew]
  exact key

end GlobalTheory.CompanionTheory.MeasureTails
