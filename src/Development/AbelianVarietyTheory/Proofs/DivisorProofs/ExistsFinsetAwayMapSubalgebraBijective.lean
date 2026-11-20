import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.Finset.Functor
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

open AlgebraicGeometry CategoryTheory Limits

namespace GlobalTheory

theorem exists_finset_awayMap_subalgebra_bijective :
    ∀ (R B : Type) [CommRing R] [CommRing B] [Algebra R B] (g : Finset B),
      (∀ b ∈ g, Algebra.FiniteType R (Localization.Away b)) →
      ∃ s : Finset B, (↑g : Set B) ⊆ ↑s ∧ ∀ C : Subalgebra R B, (↑s : Set B) ⊆ ↑C →
        ∀ b ∈ g, ∀ hb : b ∈ C,
          Function.Bijective (Localization.awayMap C.val.toRingHom (⟨b, hb⟩ : C)) := by
  intro R B _ _ _ g hg
  classical
  have key : ∀ b ∈ g, ∃ t : Finset B, ∀ C : Subalgebra R B, (↑t : Set B) ⊆ ↑C → b ∈ C →
      ∀ x : B, ∃ m : ℕ, b ^ m * x ∈ C := by
    intro b hb
    obtain ⟨t, ht⟩ := (hg b hb).out
    refine ⟨t.image fun z => (IsLocalization.sec (Submonoid.powers b) z).1, fun C hC hbC x => ?_⟩
    have main : ∀ z : Localization.Away b, ∃ (m : ℕ) (c : B), c ∈ C ∧
        z * algebraMap B _ b ^ m = algebraMap B _ c := by
      intro z
      have hz : z ∈ Algebra.adjoin R (t : Set (Localization.Away b)) := ht ▸ Algebra.mem_top
      induction hz using Algebra.adjoin_induction with
      | mem z hz =>
        obtain ⟨m, hm⟩ := (IsLocalization.sec (Submonoid.powers b) z).2.2
        refine ⟨m, (IsLocalization.sec (Submonoid.powers b) z).1, hC ?_, ?_⟩
        · simp only [Finset.coe_image]
          exact ⟨z, hz, rfl⟩
        · rw [← map_pow]
          have := IsLocalization.sec_spec (Submonoid.powers b) z
          rw [← hm] at this
          exact this
      | algebraMap r =>
        exact ⟨0, algebraMap R B r, C.algebraMap_mem r, by
          rw [pow_zero, mul_one, IsScalarTower.algebraMap_apply R B]⟩
      | add x y _ _ hx hy =>
        obtain ⟨m, c, hc, e⟩ := hx
        obtain ⟨n, d, hd, e'⟩ := hy
        refine ⟨m + n, c * b ^ n + d * b ^ m,
          add_mem (mul_mem hc (pow_mem hbC _)) (mul_mem hd (pow_mem hbC _)), ?_⟩
        rw [map_add, map_mul, map_mul, map_pow, map_pow, ← e, ← e']
        ring
      | mul x y _ _ hx hy =>
        obtain ⟨m, c, hc, e⟩ := hx
        obtain ⟨n, d, hd, e'⟩ := hy
        refine ⟨m + n, c * d, mul_mem hc hd, ?_⟩
        rw [map_mul, ← e, ← e']
        ring
    obtain ⟨m, c, hc, e⟩ := main (algebraMap B _ x)
    rw [← map_pow, ← map_mul] at e
    obtain ⟨⟨_, k, rfl⟩, hk⟩ := (IsLocalization.eq_iff_exists (Submonoid.powers b) _).1 e
    refine ⟨k + m, ?_⟩
    have : b ^ (k + m) * x = b ^ k * c := by
      have hk' : b ^ k * (x * b ^ m) = b ^ k * c := hk
      rw [← hk']; ring
    rw [this]
    exact mul_mem (pow_mem hbC _) hc
  choose! t ht using key
  refine ⟨g ∪ g.biUnion t, by simp, fun C hC b hb hbC => ⟨?_, ?_⟩⟩
  · refine (Localization.awayMap_injective_iff).2 fun a ha => ⟨0, ?_⟩
    have : a = 0 := Subtype.ext ha
    simp [this]
  · refine (Localization.awayMap_surjective_iff).2 fun x => ?_
    obtain ⟨m, hm⟩ := ht b hb C (fun y hy => hC (by
      simp only [Finset.coe_union, Finset.coe_biUnion, Set.mem_union, Set.mem_iUnion]
      exact Or.inr ⟨b, hb, hy⟩)) hbC x
    exact ⟨⟨_, hm⟩, m, rfl⟩

end GlobalTheory
