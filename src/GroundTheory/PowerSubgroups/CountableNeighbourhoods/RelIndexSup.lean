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
import Mathlib.Topology.Sheaves.Presheaf

namespace GroundTheory.Variant₂.N1

open Subgroup

theorem relIndex_sup_of_le_normalizer {G : Type*} [Group G] {H N : Subgroup G}
    (hLE : H ≤ Subgroup.normalizer (N : Set G)) : H.relIndex (H ⊔ N) = H.relIndex N := by
  symm
  let f : N →* (H ⊔ N : Subgroup G) := Subgroup.inclusion le_sup_right
  let g : N ⧸ H.subgroupOf N → (H ⊔ N : Subgroup G) ⧸ H.subgroupOf (H ⊔ N) :=
    fun q => Quotient.liftOn' q (fun n => ((f n : (H ⊔ N : Subgroup G)) :
        (H ⊔ N : Subgroup G) ⧸ H.subgroupOf (H ⊔ N))) (by
      intro a b hab
      rw [QuotientGroup.leftRel_apply, mem_subgroupOf] at hab
      rw [QuotientGroup.eq, mem_subgroupOf]
      simpa [f] using hab)
  have hinj : Function.Injective g := by
    intro x y hxy
    induction x using QuotientGroup.induction_on with
    | H a =>
    induction y using QuotientGroup.induction_on with
    | H b =>
    have h1 : ((f a : (H ⊔ N : Subgroup G)) : (H ⊔ N : Subgroup G) ⧸ H.subgroupOf (H ⊔ N)) =
        ((f b : (H ⊔ N : Subgroup G)) : (H ⊔ N : Subgroup G) ⧸ H.subgroupOf (H ⊔ N)) := hxy
    rw [QuotientGroup.eq, mem_subgroupOf] at h1
    rw [QuotientGroup.eq, mem_subgroupOf]
    simpa [f] using h1
  have hsurj : Function.Surjective g := by
    intro x
    induction x using QuotientGroup.induction_on with
    | H k =>
    obtain ⟨y, hy⟩ := k
    have hy' : y ∈ ((N ⊔ H : Subgroup G) : Set G) := by
      rw [sup_comm]; exact hy
    rw [coe_mul_of_right_le_normalizer_left N H hLE] at hy'
    obtain ⟨n, hn, h, hh, rfl⟩ := hy'
    refine ⟨((⟨n, hn⟩ : N) : N ⧸ H.subgroupOf N), ?_⟩
    change ((f ⟨n, hn⟩ : (H ⊔ N : Subgroup G)) :
        (H ⊔ N : Subgroup G) ⧸ H.subgroupOf (H ⊔ N)) = _
    rw [QuotientGroup.eq, mem_subgroupOf]
    simpa [f] using hh
  rw [Subgroup.relIndex, Subgroup.relIndex, Subgroup.index, Subgroup.index]
  exact Nat.card_congr (Equiv.ofBijective g ⟨hinj, hsurj⟩)

end GroundTheory.Variant₂.N1
