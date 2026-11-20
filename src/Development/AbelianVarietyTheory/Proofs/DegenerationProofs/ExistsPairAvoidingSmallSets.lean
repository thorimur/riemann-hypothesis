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
import Std.Tactic.BVDecide.Normalize.Prop
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory

theorem exists_notMem_of_ncard_lt_card {H : Type} [Finite H] (S : Set H)
    (h : S.ncard < Nat.card H) : ∃ x : H, x ∉ S := by
  by_contra hx
  have hS : S = Set.univ := by
    ext x
    simp only [Set.mem_univ, iff_true]
    by_contra hx'
    exact hx ⟨x, hx'⟩
  rw [hS, Set.ncard_univ] at h
  exact lt_irrefl _ h

theorem exists_pair_avoiding_small_sets :
    ∀ (H : Type) [CommGroup H] [Finite H] (B₀ B₁ : Set H), 6 * Nat.card B₀ < Nat.card H →
      6 * Nat.card B₁ < Nat.card H →
      ∃ b c : H, b ∉ B₀ ∧ c ∉ B₀ ∧ b * c ∉ B₀ ∧ b ∉ B₁ ∧ c ∉ B₁ ∧ b * c ∉ B₁ := by
  intro H _ _ B₀ B₁ h₀ h₁
  rw [Nat.card_coe_set_eq] at h₀ h₁
  have hS : (B₀ ∪ B₁).ncard ≤ B₀.ncard + B₁.ncard := Set.ncard_union_le _ _
  obtain ⟨b, hb⟩ := exists_notMem_of_ncard_lt_card (B₀ ∪ B₁) (by omega)
  have hT : ((fun x => b⁻¹ * x) '' (B₀ ∪ B₁)).ncard ≤ (B₀ ∪ B₁).ncard :=
    Set.ncard_image_le (Set.toFinite _)
  have hU : ((B₀ ∪ B₁) ∪ (fun x => b⁻¹ * x) '' (B₀ ∪ B₁)).ncard ≤
      (B₀ ∪ B₁).ncard + ((fun x => b⁻¹ * x) '' (B₀ ∪ B₁)).ncard := Set.ncard_union_le _ _
  obtain ⟨c, hc⟩ := exists_notMem_of_ncard_lt_card
    ((B₀ ∪ B₁) ∪ (fun x => b⁻¹ * x) '' (B₀ ∪ B₁)) (by omega)
  have hbc : b * c ∉ B₀ ∪ B₁ := fun h => hc (Or.inr ⟨b * c, h, by simp⟩)
  exact ⟨b, c, fun h => hb (Or.inl h), fun h => hc (Or.inl (Or.inl h)), fun h => hbc (Or.inl h),
    fun h => hb (Or.inr h), fun h => hc (Or.inl (Or.inr h)), fun h => hbc (Or.inr h)⟩

end GlobalTheory
