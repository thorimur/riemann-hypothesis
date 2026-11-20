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
import Mathlib.Tactic.Monotonicity.Lemmas
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

@[reducible] noncomputable def UpperTheory.Reformulated.B.RightCosetSpaceCompact.RightCosetSpace.{u_1} :
    {G : Type u_1} → [inst : Group G] → Subgroup G → Type u_1 :=
    fun {G : Type u_1} [Group G] (Γ : Subgroup G) ↦ Quotient (MulAction.orbitRel (↥Γ) G)

noncomputable def UpperTheory.Reformulated.B.RightCosetSpaceCompact.mk.{u_1} :
    {G : Type u_1} → [inst : Group G] → (Γ : Subgroup G) → G → UpperTheory.Reformulated.B.RightCosetSpaceCompact.RightCosetSpace Γ :=
    fun {G : Type u_1} [Group G] (Γ : Subgroup G) ↦ Quotient.mk (MulAction.orbitRel (↥Γ) G)

theorem UpperTheory.Reformulated.B.RightCosetSpaceCompact.exists_isCompact_subset_mk_image.{u_1} :
    ∀ {G : Type u_1} [inst : Group G] (Γ : Subgroup G) [inst_1 : TopologicalSpace G] [IsTopologicalGroup G]
      [LocallyCompactSpace G] {K : Set (UpperTheory.Reformulated.B.RightCosetSpaceCompact.RightCosetSpace Γ)},
      IsCompact K → ∃ (D : Set G), IsCompact D ∧ K ⊆ UpperTheory.Reformulated.B.RightCosetSpaceCompact.mk Γ '' D := by
  intro G _ Γ _ _ _ K hK
  have hopen : IsOpenMap (UpperTheory.Reformulated.B.RightCosetSpaceCompact.mk Γ) :=
    isOpenMap_quotient_mk'_mul (Γ := ↥Γ) (T := G)
  refine hK.induction_on
    (p := fun S => ∃ D : Set G, IsCompact D ∧ S ⊆ UpperTheory.Reformulated.B.RightCosetSpaceCompact.mk Γ '' D) ?_ ?_ ?_ ?_
  · exact ⟨∅, isCompact_empty, Set.empty_subset _⟩
  · rintro s t hst ⟨D, hD, htD⟩
    exact ⟨D, hD, hst.trans htD⟩
  · rintro s t ⟨D, hD, hsD⟩ ⟨E, hE, htE⟩
    refine ⟨D ∪ E, hD.union hE, ?_⟩
    rw [Set.image_union]
    exact Set.union_subset_union hsD htE
  · intro x _
    obtain ⟨g, rfl⟩ : ∃ g : G, UpperTheory.Reformulated.B.RightCosetSpaceCompact.mk Γ g = x := Quotient.exists_rep x
    obtain ⟨D, hD, hgD⟩ := exists_compact_mem_nhds g
    exact ⟨_, mem_nhdsWithin_of_mem_nhds (hopen.image_mem_nhds hgD), D, hD, subset_rfl⟩
