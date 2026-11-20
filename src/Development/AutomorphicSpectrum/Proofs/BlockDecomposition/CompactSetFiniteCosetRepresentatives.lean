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
open scoped Topology

namespace GlobalTheory.CompanionTheory.OpenSubgroupCosets

theorem exists_finset_unique_coset_reps :
    ∀ {E : Type} [AddCommGroup E] [TopologicalSpace E] [IsTopologicalAddGroup E]
      (D : AddSubgroup E), IsOpen (D : Set E) → ∀ (R : Set E), IsCompact R →
      ∃ S : Finset E, (∀ s ∈ S, s ∈ R) ∧ ∀ x ∈ R, ∃! s, s ∈ S ∧ x - s ∈ D := by
  intro E _ _ _ D hD R hR
  classical
  obtain ⟨t, ht⟩ := hR.elim_finite_subcover (fun x : E => (fun y => y - x) ⁻¹' (D : Set E))
    (fun x => hD.preimage (continuous_sub_right x))
    (fun r _ => Set.mem_iUnion.2 ⟨r, by simp⟩)
  set π : E → E ⧸ D := QuotientAddGroup.mk with hπ
  have hfin : (π '' R).Finite := by
    apply (t.finite_toSet.image π).subset
    rintro _ ⟨r, hr, rfl⟩
    obtain ⟨x, hx, hrx⟩ : ∃ x ∈ t, r - x ∈ D := by simpa using ht hr
    refine ⟨x, hx, ?_⟩
    apply QuotientAddGroup.eq_iff_sub_mem.2
    rw [← neg_sub]
    exact D.neg_mem hrx
  have hrep : ∀ c ∈ π '' R, ∃ r, r ∈ R ∧ π r = c := by
    rintro _ ⟨r, hr, rfl⟩
    exact ⟨r, hr, rfl⟩
  choose! f hfR hfπ using hrep
  refine ⟨hfin.toFinset.image f, ?_, ?_⟩
  · intro s hs
    obtain ⟨c, hc, rfl⟩ := Finset.mem_image.1 hs
    exact hfR c (hfin.mem_toFinset.1 hc)
  · intro x hx
    have hxc : π x ∈ π '' R := ⟨x, hx, rfl⟩
    refine ⟨f (π x), ⟨Finset.mem_image.2 ⟨π x, hfin.mem_toFinset.2 hxc, rfl⟩, ?_⟩, ?_⟩
    · exact QuotientAddGroup.eq_iff_sub_mem.1 (hfπ (π x) hxc).symm
    · rintro s ⟨hs, hxs⟩
      obtain ⟨c, hc, rfl⟩ := Finset.mem_image.1 hs
      have hc' := hfin.mem_toFinset.1 hc
      have h1 : π x = c := by
        rw [← hfπ c hc']
        exact QuotientAddGroup.eq_iff_sub_mem.2 hxs
      rw [h1]

end GlobalTheory.CompanionTheory.OpenSubgroupCosets
