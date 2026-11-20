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
import Std.Tactic.BVDecide.Normalize.Prop
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI GlobalTheory.Shin SemidirectProduct
open scoped Classical

namespace GlobalTheory

theorem fibre_count_comap_mul (G₀ G : Type) [Group G₀] [Group G] [Finite G₀] [Finite G]
    (ι : G₀ →* G) (H : Subgroup G) (T : G → ℂ)
    (hT : ∀ y, T y ≠ 0 → ∃ k p, p ∈ H ∧ y = ι k * p) :
    (Nat.card (H.comap ι) : ℂ) * ∑ᶠ y, T y = ∑ᶠ k : G₀, ∑ᶠ p : H, T (ι k * p) := by
  haveI : Fintype G₀ := Fintype.ofFinite G₀
  haveI : Fintype G := Fintype.ofFinite G
  have inner : ∀ k : G₀, ∑ᶠ p : H, T (ι k * p) =
      ∑ y : G, if (ι k)⁻¹ * y ∈ H then T y else 0 := by
    intro k
    rw [finsum_eq_sum_of_fintype]
    symm
    rw [← Equiv.sum_comp (Equiv.mulLeft (ι k))]
    simp only [Equiv.coe_mulLeft, inv_mul_cancel_left]
    rw [← Finset.sum_filter]
    exact Finset.sum_subtype (Finset.univ.filter (fun x : G => x ∈ H)) (by simp)
      (fun x => T (ι k * x))
  have hcount : ∀ y, T y ≠ 0 →
      ∑ k : G₀, (if (ι k)⁻¹ * y ∈ H then (1 : ℂ) else 0) = Nat.card (H.comap ι) := by
    intro y hy
    obtain ⟨k₀, p₀, hp₀, rfl⟩ := hT y hy
    rw [← Equiv.sum_comp (Equiv.mulLeft k₀)]
    simp only [Equiv.coe_mulLeft, map_mul, mul_inv_rev, mul_assoc, inv_mul_cancel_left]
    have key : ∀ m : G₀, ((ι m)⁻¹ * p₀ ∈ H ↔ m ∈ H.comap ι) := by
      intro m
      rw [Subgroup.mem_comap, ← H.inv_mem_iff (x := ι m), H.mul_mem_cancel_right hp₀]
    simp only [key]
    rw [Finset.sum_boole, Nat.card_eq_fintype_card, Fintype.card_subtype]
  rw [finsum_eq_sum_of_fintype, finsum_eq_sum_of_fintype]
  simp only [inner]
  rw [Finset.sum_comm, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun y _ => ?_)
  by_cases hy : T y = 0
  · simp [hy]
  · rw [← hcount y hy, Finset.sum_mul]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    split_ifs <;> simp

end GlobalTheory
