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

noncomputable section

open scoped Classical Pointwise
open MeasureTheory NumberField NumberField.mixedEmbedding

namespace Formalism.L2.SG.NGCut.SplitEmbedding

theorem coset_fd {V : Type} [AddCommGroup V] [MeasurableSpace V] [MeasurableAdd V] (L Λ : AddSubgroup V)
    (hle : Λ ≤ L) (hfin : (Λ.addSubgroupOf L).FiniteIndex) (FL : Set V) (hFL : MeasurableSet FL)
    (hdL : ∀ v, ∃! l : L, (l : V) + v ∈ FL) :
    ∃ G : Set V, MeasurableSet G ∧ ∀ v, ∃! a : Λ, (a : V) + v ∈ G := by
  set Λ' := Λ.addSubgroupOf L
  have : Finite (L ⧸ Λ') := Λ'.finite_quotient_of_finiteIndex
  have : Fintype (L ⧸ Λ') := Fintype.ofFinite _
  let rep : L ⧸ Λ' → L := fun q => q.out
  let G : Set V := ⋃ q : L ⧸ Λ', (fun y => ((rep q : L) : V) + y) ⁻¹' FL
  refine ⟨G, MeasurableSet.iUnion fun q => measurable_const_add _ hFL, fun v => ?_⟩
  obtain ⟨l, hl, hlu⟩ := hdL v
  set q : L ⧸ Λ' := (l : L ⧸ Λ')
  have hdiff : -(rep q) + l ∈ Λ' := by
    have : ((rep q : L) : L ⧸ Λ') = q := QuotientAddGroup.out_eq' q
    rw [← QuotientAddGroup.eq]; exact this
  have hΛ : ((-(rep q) + l : L) : V) ∈ Λ := by
    rw [AddSubgroup.mem_addSubgroupOf] at hdiff; exact hdiff
  refine ⟨⟨_, hΛ⟩, Set.mem_iUnion.2 ⟨q, ?_⟩, ?_⟩
  · show ((rep q : L) : V) + (((-(rep q) + l : L) : V) + v) ∈ FL
    simp only [AddSubgroup.coe_add, AddSubgroup.coe_neg]
    rw [← add_assoc, add_neg_cancel_left]; exact hl
  · rintro ⟨a, ha⟩ haG
    obtain ⟨q', hq'⟩ := Set.mem_iUnion.1 haG
    have hq'' : ((rep q' : L) : V) + (a + v) ∈ FL := hq'
    have hmem : ((rep q' : V) + a) ∈ L := L.add_mem (rep q').2 (hle ha)
    have h1 : (⟨(rep q' : V) + a, hmem⟩ : L) = l := hlu _ (by show (rep q' : V) + a + v ∈ FL; rw [add_assoc]; exact hq'')

    have hqq : q' = q := by
      have e : (rep q' : L) + ⟨a, hle ha⟩ = l := by
        apply Subtype.ext; simpa using congrArg Subtype.val h1
      have hmk : ((l : L) : L ⧸ Λ') = ((rep q' : L) : L ⧸ Λ') := by
        rw [← e, QuotientAddGroup.eq]
        simp only [neg_add_rev, neg_add_cancel_right]
        rw [AddSubgroup.mem_addSubgroupOf]
        simpa using Λ.neg_mem ha
      rw [show ((rep q' : L) : L ⧸ Λ') = q' from QuotientAddGroup.out_eq' q'] at hmk
      exact hmk.symm
    apply Subtype.ext
    show a = ((-(rep q) + l : L) : V)
    have := congrArg Subtype.val h1
    simp only at this
    rw [← hqq]
    simp only [AddSubgroup.coe_add, AddSubgroup.coe_neg]
    rw [← this]
    abel

end Formalism.L2.SG.NGCut.SplitEmbedding
