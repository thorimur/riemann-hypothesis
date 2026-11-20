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
open MeasureTheory

namespace GlobalTheory.CompanionTheory.BigCell

theorem prod_coordinate_bumps :
    ∀ (G A ι : Type) [AddCommGroup G] [TopologicalSpace G] [AddCommGroup A] [TopologicalSpace A]
      [T2Space A] [Fintype ι] (e : G ≃ₜ+ (ι → A)) (ρ : ℕ → A → ℝ),
      (∀ k, Continuous (ρ k) ∧ HasCompactSupport (ρ k) ∧ ∀ y, 0 ≤ ρ k y) →
      Filter.Tendsto (fun k => tsupport (ρ k)) Filter.atTop (nhds (0 : A)).smallSets →
      (∀ k, Continuous (fun T : G => ∏ i, ρ k (e T i)) ∧
        HasCompactSupport (fun T : G => ∏ i, ρ k (e T i)) ∧
        ∀ T : G, 0 ≤ ∏ i, ρ k (e T i)) ∧
      Filter.Tendsto (fun k => tsupport (fun T : G => ∏ i, ρ k (e T i))) Filter.atTop
        (nhds (0 : G)).smallSets := by
  intro G A ι _ _ _ _ _ _ e ρ hρ hlim
  have hsub : ∀ k, tsupport (fun T : G => ∏ i, ρ k (e T i)) ⊆
      e ⁻¹' (Set.univ.pi fun _ => tsupport (ρ k)) := by
    intro k
    apply closure_minimal
    · intro T hT
      simp only [Set.mem_preimage, Set.mem_univ_pi]
      intro i
      apply subset_tsupport
      rw [Function.mem_support] at hT ⊢
      exact (Finset.prod_ne_zero_iff.mp hT) i (Finset.mem_univ i)
    · exact (isClosed_set_pi fun i _ => isClosed_tsupport (ρ k)).preimage (map_continuous e)
  refine ⟨fun k => ⟨?_, ?_, fun T => Finset.prod_nonneg fun i _ => (hρ k).2.2 _⟩, ?_⟩
  · exact continuous_finsetProd _ fun i _ => (hρ k).1.comp ((continuous_apply i).comp (map_continuous e))
  · have hS : IsCompact (e ⁻¹' (Set.univ.pi fun _ => tsupport (ρ k))) :=
      (Homeomorph.isCompact_preimage (e : G ≃ₜ (ι → A))).mpr (isCompact_univ_pi fun _ => (hρ k).2.1)
    exact IsCompact.of_isClosed_subset hS (isClosed_tsupport _) (hsub k)
  · rw [Filter.tendsto_smallSets_iff] at hlim ⊢
    intro U hU
    have hV : e.symm ⁻¹' U ∈ nhds (0 : ι → A) :=
      (map_continuous e.symm).continuousAt.preimage_mem_nhds (by rwa [map_zero])
    rw [nhds_pi, Filter.mem_pi] at hV
    obtain ⟨I, -, t, ht, hIt⟩ := hV
    have hW : (⋂ i, t i) ∈ nhds (0 : A) := Filter.iInter_mem.mpr fun i => by simpa using ht i
    filter_upwards [hlim _ hW] with k hk
    intro T hT
    have h1 := hsub k hT
    simp only [Set.mem_preimage, Set.mem_univ_pi] at h1
    have h2 : e T ∈ I.pi t := fun i _ => Set.mem_iInter.mp (hk (h1 i)) i
    simpa using hIt h2

end GlobalTheory.CompanionTheory.BigCell
