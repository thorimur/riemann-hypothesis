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

namespace Bl.FirstLemmaC

theorem goal1 :
  ∀ {G : Type} [inst : Group.{0} G] [inst_1 : TopologicalSpace.{0} G] [IsTopologicalGroup.{0} G] (L : Subgroup.{0} G),
  IsOpen.{0} (SetLike.coe.{0, 0} L) →
    ∀ (t : G),
      IsCompact.{0} (closure.{0} (SetLike.coe.{0, 0} (Subgroup.zpowers.{0} t))) →
        Exists.{1} fun (k : Nat) ↦ And (LT.lt.{0} 0 k) (Membership.mem.{0, 0} L (HPow.hPow.{0, 0, 0} t k))  := by
  intro G _ _ _ L hL t hK
  have : DiscreteTopology (G ⧸ L) := QuotientGroup.discreteTopology hL
  have hfin : ((QuotientGroup.mk : G → G ⧸ L) '' closure (Subgroup.zpowers t : Set G)).Finite :=
    (hK.image QuotientGroup.continuous_mk).finite_of_discrete
  have := hfin.to_subtype
  let f : ℕ → ((QuotientGroup.mk : G → G ⧸ L) '' closure (Subgroup.zpowers t : Set G)) :=
    fun n => ⟨QuotientGroup.mk (t ^ n), t ^ n, subset_closure (Subgroup.npow_mem_zpowers t n), rfl⟩
  obtain ⟨a, b, hab, he⟩ := Finite.exists_ne_map_eq_of_infinite f
  have h2 : (t ^ a)⁻¹ * t ^ b ∈ L := QuotientGroup.eq.mp (congrArg Subtype.val he)
  rcases lt_or_gt_of_ne hab with h | h
  · obtain ⟨c, rfl⟩ := Nat.exists_eq_add_of_lt h
    refine ⟨c + 1, Nat.succ_pos c, ?_⟩
    rwa [add_assoc, pow_add, inv_mul_cancel_left] at h2
  · obtain ⟨c, rfl⟩ := Nat.exists_eq_add_of_lt h
    have h3 := L.inv_mem h2
    refine ⟨c + 1, Nat.succ_pos c, ?_⟩
    rwa [mul_inv_rev, inv_inv, add_assoc, pow_add, inv_mul_cancel_left] at h3

end Bl.FirstLemmaC
