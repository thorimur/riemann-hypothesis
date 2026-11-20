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
import Mathlib.Tactic.ENatToNat
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

namespace GlobalTheory

theorem exists_finset_leftTransversal_of_relIndex_ne_zero : ∀ {G : Type} [Group G] (H K : Subgroup G),
    K ≤ H → K.relIndex H ≠ 0 → ∃ R : Finset G, (∀ r ∈ R, r ∈ H) ∧ ∀ k ∈ H, ∃! r, r ∈ R ∧ r⁻¹ * k ∈ K := by
  intro G _ H K _ hrel
  have hfin : Finite (H ⧸ K.subgroupOf H) := by
    apply Nat.finite_of_card_ne_zero
    simpa [Subgroup.relIndex, Subgroup.index] using hrel
  let f : H ⧸ K.subgroupOf H → G := fun q => ((Quotient.out q : H) : G)
  have hR : (Set.range f).Finite := Set.finite_range f
  refine ⟨hR.toFinset, ?_, ?_⟩
  · intro r hr
    rw [Set.Finite.mem_toFinset] at hr
    obtain ⟨q, rfl⟩ := hr
    exact (Quotient.out q : H).2
  · intro k hk
    refine ⟨f (QuotientGroup.mk (⟨k, hk⟩ : H)), ⟨?_, ?_⟩, ?_⟩
    · rw [Set.Finite.mem_toFinset]; exact ⟨_, rfl⟩
    · have h1 : (QuotientGroup.mk (Quotient.out (QuotientGroup.mk (⟨k, hk⟩ : H) : H ⧸ K.subgroupOf H)) :
          H ⧸ K.subgroupOf H) = QuotientGroup.mk ⟨k, hk⟩ := QuotientGroup.out_eq' _
      rw [QuotientGroup.eq, Subgroup.mem_subgroupOf] at h1
      simpa [f] using h1
    · rintro r ⟨hr, hrk⟩
      rw [Set.Finite.mem_toFinset] at hr
      obtain ⟨q, rfl⟩ := hr
      have h2 : (QuotientGroup.mk (Quotient.out q) : H ⧸ K.subgroupOf H) = QuotientGroup.mk ⟨k, hk⟩ := by
        rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
        simpa [f] using hrk
      rw [QuotientGroup.out_eq'] at h2
      simp [f, h2]

end GlobalTheory
