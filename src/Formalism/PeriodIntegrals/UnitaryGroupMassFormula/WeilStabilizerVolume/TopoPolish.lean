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
import Mathlib.Topology.Compactification.OnePoint.Basic
import Mathlib.Topology.Separation.CompletelyRegular
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop

noncomputable section

namespace PI.VolStabW.TopoPolish

open Topology TopologicalSpace Set

theorem polish_of_lcsc (Y : Type) [TopologicalSpace Y] [LocallyCompactSpace Y] [T2Space Y]
    [SecondCountableTopology Y] : PolishSpace Y := by

  haveI hS : SecondCountableTopology (OnePoint Y) := by

    let K := CompactExhaustion.choice Y
    let B : Set (Set (OnePoint Y)) :=
      ((fun U => ((↑) : Y → OnePoint Y) '' U) '' countableBasis Y) ∪
        Set.range (fun n => (((↑) : Y → OnePoint Y) '' K n)ᶜ)
    have hB : IsTopologicalBasis B := by
      refine isTopologicalBasis_of_isOpen_of_nhds ?_ ?_
      · rintro u (⟨U, hU, rfl⟩ | ⟨n, rfl⟩)
        · exact OnePoint.isOpen_image_coe.2 ((isBasis_countableBasis Y).isOpen hU)
        · exact OnePoint.isOpen_compl_image_coe.2 ⟨(K.isCompact n).isClosed, K.isCompact n⟩
      · intro a u ha hu
        induction a using OnePoint.rec with
        | infty =>
          rw [OnePoint.isOpen_iff_of_mem ha] at hu
          obtain ⟨n, hn⟩ := K.exists_superset_of_isCompact hu.2
          refine ⟨_, Or.inr ⟨n, rfl⟩, ?_, ?_⟩
          · simp
          · intro z hz
            induction z using OnePoint.rec with
            | infty => exact ha
            | coe y =>
              by_contra hyu
              exact hz ⟨y, hn hyu, rfl⟩
        | coe y =>
          have hpre : IsOpen (((↑) : Y → OnePoint Y) ⁻¹' u) := hu.preimage OnePoint.continuous_coe
          obtain ⟨U, hU, hyU, hUu⟩ :=
            (isBasis_countableBasis Y).exists_subset_of_mem_open (show y ∈ _ from ha) hpre
          exact ⟨_, Or.inl ⟨U, hU, rfl⟩, ⟨y, hyU, rfl⟩, by rintro _ ⟨z, hz, rfl⟩; exact hUu hz⟩
    exact hB.secondCountableTopology
      (((countable_countableBasis Y).image _).union (Set.countable_range _))
  haveI hM : MetrizableSpace (OnePoint Y) := by
    first
    | infer_instance
    | exact TopologicalSpace.metrizableSpace_of_t3_secondCountable _
  haveI hP : PolishSpace (OnePoint Y) := by
    first
    | infer_instance
    | (letI := TopologicalSpace.metrizableSpaceMetric (OnePoint Y)
       haveI : CompleteSpace (OnePoint Y) := complete_of_compact
       infer_instance)
  have hO : IsOpen (Set.range ((↑) : Y → OnePoint Y)) := OnePoint.isOpen_range_coe
  haveI := hO.polishSpace
  first
  | exact (OnePoint.isOpenEmbedding_coe.toIsEmbedding.toHomeomorph).isClosedEmbedding.polishSpace
  | exact (OnePoint.isOpenEmbedding_coe.isEmbedding.toHomeomorph).isClosedEmbedding.polishSpace
  | exact (OnePoint.isOpenEmbedding_coe.toHomeomorph).isClosedEmbedding.polishSpace

end PI.VolStabW.TopoPolish
