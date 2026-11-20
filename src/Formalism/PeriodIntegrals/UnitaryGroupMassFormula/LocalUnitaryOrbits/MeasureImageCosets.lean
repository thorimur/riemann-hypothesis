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

namespace PI.OmLocU

open MeasureTheory

theorem measure_image_cosets {V : Type} [AddCommGroup V] [MeasurableSpace V] [MeasurableAdd V]
    (μ : Measure V) [μ.IsAddLeftInvariant] (H L : AddSubgroup V) (hHL : H ≤ L)
    (hH : MeasurableSet (H : Set V)) (hfin : H.relIndex L ≠ 0) (S : Set L)
    (hS : ∀ x ∈ S, ∀ y : L, (y : V) ∈ H → x + y ∈ S) :
    μ (((↑) : L → V) '' S) =
      (Nat.card (QuotientAddGroup.mk '' S : Set (L ⧸ H.addSubgroupOf L)) : ENNReal) * μ H := by
  classical
  set H' := H.addSubgroupOf L with hH'
  haveI : H'.FiniteIndex := ⟨hfin⟩
  set T : Set (L ⧸ H') := QuotientAddGroup.mk '' S with hT
  have hTfin : T.Finite := Set.toFinite T
  have hr : ∀ t ∈ T, ∃ x ∈ S, (QuotientAddGroup.mk x : L ⧸ H') = t := fun t ht => ht
  choose! r hrS hrt using hr
  let C : L ⧸ H' → Set V := fun t => (fun v => -((r t : L) : V) + v) ⁻¹' (H : Set V)
  have hCm : ∀ t, MeasurableSet (C t) := fun t => measurable_const_add _ hH
  have hCμ : ∀ t, μ (C t) = μ H := fun t => measure_preimage_add μ _ _
  have hU : ((↑) : L → V) '' S = ⋃ t ∈ hTfin.toFinset, C t := by
    ext v
    simp only [Set.mem_image, Set.mem_iUnion, Set.Finite.mem_toFinset, exists_prop]
    constructor
    · rintro ⟨x, hx, rfl⟩
      refine ⟨QuotientAddGroup.mk x, ⟨x, hx, rfl⟩, ?_⟩
      have e := hrt _ ⟨x, hx, rfl⟩
      rw [QuotientAddGroup.eq] at e
      have e' : ((-(r (QuotientAddGroup.mk x)) + x : L) : V) ∈ H := e
      simpa [C] using e'
    · rintro ⟨t, ht, hv⟩
      have hvH : -((r t : L) : V) + v ∈ H := hv
      refine ⟨r t + ⟨-((r t : L) : V) + v, hHL hvH⟩, hS _ (hrS t ht) _ hvH, ?_⟩
      simp
  rw [hU, measure_biUnion_finset]
  · simp only [hCμ, Finset.sum_const, nsmul_eq_mul]
    congr 1
    rw [Nat.card_coe_set_eq, Set.ncard_eq_toFinset_card T hTfin]
  · intro t ht t' ht' hne
    have ht1 : t ∈ T := hTfin.mem_toFinset.mp ht
    have ht2 : t' ∈ T := hTfin.mem_toFinset.mp ht'
    refine Set.disjoint_left.mpr fun v hv hv' => hne ?_
    rw [← hrt t ht1, ← hrt t' ht2, QuotientAddGroup.eq]
    show ((-(r t) + r t' : L) : V) ∈ H
    have hs := H.sub_mem (show -((r t : L) : V) + v ∈ H from hv) (show -((r t' : L) : V) + v ∈ H from hv')
    convert hs using 1
    push_cast
    abel
  · exact fun t _ => hCm t

end PI.OmLocU
