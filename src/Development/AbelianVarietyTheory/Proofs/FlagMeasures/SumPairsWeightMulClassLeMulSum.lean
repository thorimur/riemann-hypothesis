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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

open scoped Classical

namespace GlobalTheory

theorem sum_pairs_weight_mul_class_le_mul_sum (α β : Type) (S : Finset (α × α)) (cls : α → β)
    (w : α → ℝ) (om : β → ℝ) (T₁ T₂ : Finset β) (hw : ∀ a, 0 ≤ w a) (hom : ∀ b, 0 ≤ om b)
    (hT : ∀ p ∈ S, cls p.1 ∈ T₁ ∧ cls p.2 ∈ T₂)
    (hinj : ∀ p ∈ S, ∀ q ∈ S, p.1 = q.1 → cls p.2 = cls q.2 → p = q)
    (hsum : ∀ b, ∑ a ∈ (S.image Prod.fst).filter (fun a => cls a = b), w a ≤ 1) :
    ∑ p ∈ S, w p.1 * (om (cls p.1) * om (cls p.2)) ≤ (∑ b ∈ T₁, om b) * ∑ b ∈ T₂, om b := by

  have key : ∀ b ∈ T₁ ×ˢ T₂,
      ∑ p ∈ S.filter (fun p => (cls p.1, cls p.2) = b), w p.1 * (om (cls p.1) * om (cls p.2))
        ≤ om b.1 * om b.2 := by
    intro b _
    set F := S.filter (fun p => (cls p.1, cls p.2) = b) with hF
    have h1 : ∑ p ∈ F, w p.1 * (om (cls p.1) * om (cls p.2))
        = (∑ p ∈ F, w p.1) * (om b.1 * om b.2) := by
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl ?_
      intro p hp
      have e := (Finset.mem_filter.1 hp).2
      rw [← e]
    have h2 : ∑ p ∈ F, w p.1 = ∑ a ∈ F.image Prod.fst, w a := by
      rw [Finset.sum_image]
      intro p hp q hq hpq
      have ep := (Finset.mem_filter.1 hp).2
      have eq := (Finset.mem_filter.1 hq).2
      have hc : cls p.2 = cls q.2 := by
        have := congrArg Prod.snd (ep.trans eq.symm)
        simpa using this
      exact hinj p (Finset.mem_filter.1 hp).1 q (Finset.mem_filter.1 hq).1 hpq hc
    have h3 : F.image Prod.fst ⊆ (S.image Prod.fst).filter (fun a => cls a = b.1) := by
      intro a ha
      obtain ⟨p, hp, rfl⟩ := Finset.mem_image.1 ha
      have hp' := Finset.mem_filter.1 hp
      refine Finset.mem_filter.2 ⟨Finset.mem_image_of_mem _ hp'.1, ?_⟩
      have := congrArg Prod.fst hp'.2
      simpa using this
    have h4 : ∑ p ∈ F, w p.1 ≤ 1 := by
      rw [h2]
      exact (Finset.sum_le_sum_of_subset_of_nonneg h3 (fun a _ _ => hw a)).trans (hsum b.1)
    rw [h1]
    have hnn : 0 ≤ om b.1 * om b.2 := mul_nonneg (hom _) (hom _)
    calc (∑ p ∈ F, w p.1) * (om b.1 * om b.2) ≤ 1 * (om b.1 * om b.2) :=
          mul_le_mul_of_nonneg_right h4 hnn
      _ = om b.1 * om b.2 := one_mul _
  calc ∑ p ∈ S, w p.1 * (om (cls p.1) * om (cls p.2))
      = ∑ b ∈ T₁ ×ˢ T₂, ∑ p ∈ S.filter (fun p => (cls p.1, cls p.2) = b),
          w p.1 * (om (cls p.1) * om (cls p.2)) := by
        symm
        exact Finset.sum_fiberwise_of_maps_to (fun p hp => Finset.mem_product.2 (hT p hp)) _
    _ ≤ ∑ b ∈ T₁ ×ˢ T₂, om b.1 * om b.2 := Finset.sum_le_sum key
    _ = (∑ b ∈ T₁, om b) * ∑ b ∈ T₂, om b := by
      rw [Finset.sum_product, Finset.sum_mul]
      refine Finset.sum_congr rfl (fun x _ => ?_)
      rw [Finset.mul_sum]

end GlobalTheory
