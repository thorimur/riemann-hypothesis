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

noncomputable def UpperTheory.Reformulated.B.DYhc7.Iwa :
    {G : Type} → [inst : Group G] → Subgroup G → Subgroup G → Prop :=
    fun {G : Type} [Group G] (P K : Subgroup G) ↦ ∀ (g : G), ∃ p ∈ P, ∃ k ∈ K, g = p * k

theorem UpperTheory.Reformulated.B.DYhc7.main :
    ∀ {G : Type} [inst : Group G] [inst_1 : TopologicalSpace G] [IsTopologicalGroup G] {K P : Subgroup G},
      IsCompact (↑K : Set G) →
        IsClosed (↑P : Set G) →
          UpperTheory.Reformulated.B.DYhc7.Iwa P K → Topology.IsQuotientMap fun (x : ↥P × ↥K) ↦ (↑x.1 : G) * (↑x.2 : G) := by
  intro G _ _ _ K P hK hP hI
  haveI : CompactSpace K := isCompact_iff_compactSpace.mp hK
  let h : G × K ≃ₜ G × K :=
    { toFun := fun y => (y.1 * (y.2 : G), y.2)
      invFun := fun y => (y.1 * (y.2 : G)⁻¹, y.2)
      left_inv := fun y => by simp
      right_inv := fun y => by simp
      continuous_toFun := by fun_prop
      continuous_invFun := by fun_prop }
  have hι : Topology.IsClosedEmbedding (Prod.map (Subtype.val : P → G) (id : K → K)) :=
    hP.isClosedEmbedding_subtypeVal.prodMap Topology.IsClosedEmbedding.id
  have hcl : IsClosedMap (fun x : ↥P × ↥K ↦ (x.1 : G) * (x.2 : G)) := by
    have h1 : IsClosedMap (Prod.fst : G × K → G) := isClosedMap_fst_of_compactSpace
    exact h1.comp (h.isClosedMap.comp hι.isClosedMap)
  refine hcl.isQuotientMap (by fun_prop) ?_
  intro g
  obtain ⟨p, hp, k, hk, rfl⟩ := hI g
  exact ⟨(⟨p, hp⟩, ⟨k, hk⟩), rfl⟩
