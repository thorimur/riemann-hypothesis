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
import Mathlib.RingTheory.PiTensorProduct
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
import Mathlib.Topology.Sheaves.Init
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory

theorem algHom_eq_mul_pow_of_eq_localizationAway :
    ∀ (R' A S : Type) [CommRing R'] [CommRing A] [CommRing S] [Algebra R' A] [Algebra R' S]
    [Algebra.FiniteType R' A] (χ₁ χ₂ : A →ₐ[R'] S) (g : S),
    (∀ x, algebraMap S (Localization.Away g) (χ₁ x) = algebraMap S (Localization.Away g) (χ₂ x)) →
    ∃ N : ℕ, ∀ x, g ^ N * χ₁ x = g ^ N * χ₂ x := by
  intro R' A S _ _ _ _ _ _ χ₁ χ₂ g h
  have key : ∀ x, ∃ n : ℕ, g ^ n * χ₁ x = g ^ n * χ₂ x := by
    intro x
    obtain ⟨⟨c, hc⟩, hcx⟩ :=
      (IsLocalization.eq_iff_exists (Submonoid.powers g) (Localization.Away g)).1 (h x)
    obtain ⟨n, rfl⟩ := Submonoid.mem_powers_iff _ _ |>.1 hc
    exact ⟨n, hcx⟩
  choose n hn using key
  obtain ⟨s, hs⟩ := (Algebra.FiniteType.out : (⊤ : Subalgebra R' A).FG)
  refine ⟨∑ x ∈ s, n x, fun x => ?_⟩
  set N := ∑ x ∈ s, n x
  have hx : x ∈ Algebra.adjoin R' (s : Set A) := by rw [hs]; exact Algebra.mem_top
  induction hx using Algebra.adjoin_induction with
  | mem x hxs =>
    have hle : n x ≤ N := Finset.single_le_sum (fun _ _ => Nat.zero_le _) hxs
    rw [← Nat.sub_add_cancel hle, pow_add, mul_assoc, mul_assoc, hn x]
  | algebraMap r => rw [AlgHom.commutes, AlgHom.commutes]
  | add x y _ _ hx hy => rw [map_add, map_add, mul_add, mul_add, hx, hy]
  | mul x y _ _ hx hy =>
    rw [map_mul, map_mul]
    calc g ^ N * (χ₁ x * χ₁ y) = χ₁ x * (g ^ N * χ₁ y) := by ring
      _ = χ₁ x * (g ^ N * χ₂ y) := by rw [hy]
      _ = (g ^ N * χ₁ x) * χ₂ y := by ring
      _ = (g ^ N * χ₂ x) * χ₂ y := by rw [hx]
      _ = g ^ N * (χ₂ x * χ₂ y) := by ring

end GlobalTheory
