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

open Filter Topology

namespace GlobalTheory.CompanionTheory.Ar.PB

theorem tendsto_limUnder_of_cauchy_rate :
    ∀ (f δ : ℝ → ℝ) (t₁ : ℝ), 0 < t₁ → Filter.Tendsto δ (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) →
      (∀ t t', 0 < t' → t' ≤ t → t ≤ t₁ → |f t - f t'| ≤ δ t) →
      Filter.Tendsto f (nhdsWithin 0 (Set.Ioi 0))
          (nhds (Filter.limUnder (nhdsWithin 0 (Set.Ioi 0)) f)) ∧
        ∀ t, 0 < t → t ≤ t₁ → |f t - Filter.limUnder (nhdsWithin 0 (Set.Ioi 0)) f| ≤ δ t := by
  intro f δ t₁ ht₁ hδ hrate
  set F : Filter ℝ := nhdsWithin 0 (Set.Ioi 0) with hF

  have hS : ∀ ε > 0, {t | δ t < ε ∧ 0 < t ∧ t ≤ t₁} ∈ F := fun ε hε =>
    Filter.inter_mem (hδ (Iio_mem_nhds hε))
      (Filter.inter_mem self_mem_nhdsWithin (mem_nhdsWithin_of_mem_nhds (Iic_mem_nhds ht₁)))
  have hC : Cauchy (Filter.map f F) := by
    rw [Metric.cauchy_iff]
    refine ⟨inferInstance, fun ε hε => ⟨f '' {t | δ t < ε ∧ 0 < t ∧ t ≤ t₁}, Filter.image_mem_map (hS ε hε), ?_⟩⟩
    rintro _ ⟨t, ⟨h1, h2, h3⟩, rfl⟩ _ ⟨t', ⟨h1', h2', h3'⟩, rfl⟩
    rw [Real.dist_eq]
    rcases le_total t' t with h | h
    · exact (hrate t t' h2' h h3).trans_lt h1
    · rw [abs_sub_comm]; exact (hrate t' t h2 h h3').trans_lt h1'
  obtain ⟨L, hL⟩ := CompleteSpace.complete hC
  have hlim : Filter.Tendsto f F (nhds (Filter.limUnder F f)) := tendsto_nhds_limUnder ⟨L, hL⟩
  refine ⟨hlim, fun t ht htt => ?_⟩

  have hev : ∀ᶠ t' in F, |f t - f t'| ≤ δ t := by
    filter_upwards [self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds (Iic_mem_nhds ht)] with t' h0 h1
    exact hrate t t' h0 h1 htt
  exact le_of_tendsto (tendsto_const_nhds.sub hlim).abs hev

end GlobalTheory.CompanionTheory.Ar.PB
