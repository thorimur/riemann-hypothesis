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
import Mathlib.Topology.Compactification.OnePoint.Basic
import Mathlib.Topology.Separation.CompletelyRegular
import Mathlib.Topology.Sheaves.Init

noncomputable section

namespace PI.VolStabS.TopoPolish

open Topology TopologicalSpace Set

theorem polish_of_lcsc (Y : Type) [TopologicalSpace Y] [LocallyCompactSpace Y] [T2Space Y]
    [SecondCountableTopology Y] : PolishSpace Y := by
  classical
  let K := CompactExhaustion.choice Y
  let b : Set (Set (OnePoint Y)) :=
    ((fun s : Set Y => ((↑) : Y → OnePoint Y) '' s) '' countableBasis Y) ∪
      Set.range (fun m : ℕ => (((↑) : Y → OnePoint Y) '' K m)ᶜ)
  have hopen : ∀ m, IsOpen ((((↑) : Y → OnePoint Y) '' K m)ᶜ) := fun m =>
    OnePoint.isOpen_compl_image_coe.mpr ⟨(K.isCompact m).isClosed, K.isCompact m⟩
  have hb : IsTopologicalBasis b := by
    refine isTopologicalBasis_of_isOpen_of_nhds ?_ ?_
    · rintro u (⟨s, hs, rfl⟩ | ⟨m, rfl⟩)
      · exact OnePoint.isOpenEmbedding_coe.isOpenMap _ (isOpen_of_mem_countableBasis hs)
      · exact hopen m
    · intro a u ha hu
      induction a using OnePoint.rec with
      | infty =>
        have hc := (OnePoint.isOpen_iff_of_mem ha).mp hu
        obtain ⟨m, hm⟩ := K.exists_superset_of_isCompact hc.2
        refine ⟨_, Or.inr ⟨m, rfl⟩, ?_, ?_⟩
        · rintro ⟨y, -, hy⟩
          exact OnePoint.coe_ne_infty y hy
        · intro x hx
          induction x using OnePoint.rec with
          | infty => exact ha
          | coe y =>
            by_contra hyu
            exact hx ⟨y, hm hyu, rfl⟩
      | coe y =>
        have hu' : IsOpen (((↑) : Y → OnePoint Y) ⁻¹' u) := hu.preimage OnePoint.continuous_coe
        obtain ⟨v, hv, hyv, hvu⟩ :=
          (isBasis_countableBasis Y).exists_subset_of_mem_open (show y ∈ _ from ha) hu'
        refine ⟨_, Or.inl ⟨v, hv, rfl⟩, ⟨y, hyv, rfl⟩, ?_⟩
        rintro _ ⟨z, hz, rfl⟩
        exact hvu hz
  haveI : SecondCountableTopology (OnePoint Y) :=
    hb.secondCountableTopology (((countable_countableBasis Y).image _).union (Set.countable_range _))
  haveI : PolishSpace (OnePoint Y) := by
    haveI : MetrizableSpace (OnePoint Y) := metrizableSpace_of_t3_secondCountable _
    letI := metrizableSpaceMetric (OnePoint Y)
    haveI : CompleteSpace (OnePoint Y) := complete_of_compact
    infer_instance
  haveI : PolishSpace (Set.range ((↑) : Y → OnePoint Y)) := OnePoint.isOpen_range_coe.polishSpace
  exact (OnePoint.isOpenEmbedding_coe.isEmbedding.toHomeomorph).isClosedEmbedding.polishSpace

end PI.VolStabS.TopoPolish
