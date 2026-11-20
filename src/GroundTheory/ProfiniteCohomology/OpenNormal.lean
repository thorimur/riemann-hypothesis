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
import Mathlib.Topology.Algebra.ClopenNhdofOne
import Mathlib.Topology.Sheaves.Init
set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open Filter Topology

variable {G : Type*} [Group G] [TopologicalSpace G]

namespace OpenNormalSubgroup

instance instNonempty : Nonempty (OpenNormalSubgroup G) :=
  ⟨{ toOpenSubgroup := ⊤, isNormal' := ⟨fun _ _ _ => Set.mem_univ _⟩ }⟩

theorem mem_nhds_one (U : OpenNormalSubgroup G) : (U : Set G) ∈ 𝓝 (1 : G) :=
  U.toOpenSubgroup.isOpen.mem_nhds U.one_mem

variable [IsTopologicalGroup G]

instance discreteTopology_quotient (U : OpenNormalSubgroup G) :
    DiscreteTopology (G ⧸ (U : Subgroup G)) :=
  QuotientGroup.discreteTopology U.toOpenSubgroup.isOpen

instance finite_quotient [CompactSpace G] (U : OpenNormalSubgroup G) :
    Finite (G ⧸ (U : Subgroup G)) :=
  Subgroup.quotient_finite_of_isOpen _ U.toOpenSubgroup.isOpen

variable [CompactSpace G] [TotallyDisconnectedSpace G]

theorem hasBasis_nhds_one :
    (𝓝 (1 : G)).HasBasis (fun _ : OpenNormalSubgroup G => True) (fun U => (U : Set G)) := by
  refine ⟨fun s => ⟨fun hs => ?_, fun ⟨U, _, hU⟩ => mem_of_superset U.mem_nhds_one hU⟩⟩
  obtain ⟨t, hts, ht, h1⟩ := mem_nhds_iff.mp hs
  obtain ⟨U, hU⟩ := ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one ht h1
  exact ⟨U, trivial, hU.trans hts⟩

theorem hasBasis_nhds_one_pi (ι : Type*) [Finite ι] :
    (𝓝 (1 : ι → G)).HasBasis (fun _ : OpenNormalSubgroup G => True)
      (fun U => Set.univ.pi fun _ => (U : Set G)) := by
  simp only [nhds_pi, Pi.one_apply]
  refine (hasBasis_nhds_one.pi_self (ι := ι)).to_hasBasis ?_ ?_
  · rintro ⟨I, U⟩ -
    exact ⟨U, trivial, fun x hx i _ => hx i (Set.mem_univ i)⟩
  · intro U _
    exact ⟨⟨Set.univ, U⟩, ⟨Set.finite_univ, trivial⟩, subset_rfl⟩

end OpenNormalSubgroup

end GroundTheory.ProfCoh
