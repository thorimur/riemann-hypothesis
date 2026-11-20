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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

theorem UpperTheory.involution_map_compact_finite :
    ∀ (X : Type) [TopologicalSpace X] [T2Space X] [MeasurableSpace X] [OpensMeasurableSpace X] (μ : MeasureTheory.Measure X) (U : Set X) (ι : X → X), Measurable ι → IsClosed U → ContinuousOn ι U → (∀ x ∈ U, ι x ∈ U) → (∀ x ∈ U, ι (ι x) = x) → μ Uᶜ = 0 → (∀ K : Set X, IsCompact K → μ K < ⊤) → ∀ K : Set X, IsCompact K → (μ.map ι) K < ⊤ := by
  intro X _ _ _ _ μ U ι hm hU hc hmaps hinv h0 hfin K hK
  rw [MeasureTheory.Measure.map_apply hm hK.measurableSet]
  have hcomp : IsCompact (ι '' (K ∩ U)) :=
    (hK.inter_right hU).image_of_continuousOn (hc.mono Set.inter_subset_right)
  have hsub : ι ⁻¹' K ⊆ ι '' (K ∩ U) ∪ Uᶜ := by
    intro x hx
    by_cases hxU : x ∈ U
    · exact Or.inl ⟨ι x, ⟨hx, hmaps x hxU⟩, hinv x hxU⟩
    · exact Or.inr hxU
  calc μ (ι ⁻¹' K) ≤ μ (ι '' (K ∩ U) ∪ Uᶜ) := MeasureTheory.measure_mono hsub
    _ ≤ μ (ι '' (K ∩ U)) + μ Uᶜ := MeasureTheory.measure_union_le _ _
    _ = μ (ι '' (K ∩ U)) := by rw [h0, add_zero]
    _ < ⊤ := hfin _ hcomp
