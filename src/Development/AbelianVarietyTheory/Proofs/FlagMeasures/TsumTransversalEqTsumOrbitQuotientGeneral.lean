import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.CStarAlgebra.Classes
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
open scoped ENNReal Classical

namespace GlobalTheory

theorem tsum_transversal_eq_tsum_orbitQuotient_general {G X A M : Type} [Group G] [MulAction G X]
    [AddCommMonoid M] [TopologicalSpace M] (ι : A → X) (T : X → Prop)
    (hT : ∀ g : G, ∀ x, T x → T (g • x)) (hι : ∀ a, T (ι a))
    (hsurj : ∀ x, T x → ∃ a, ∃ g : G, g • ι a = x)
    (hinj : ∀ a b, (∃ g : G, g • ι a = ι b) → a = b)
    (φ : X → M) (hφ : ∀ g : G, ∀ x, T x → φ (g • x) = φ x) :
    ∑' a, φ (ι a) = ∑' o : MulAction.orbitRel.Quotient G X, if T o.out then φ o.out else 0 := by
  let c : A → MulAction.orbitRel.Quotient G X := fun a => Quotient.mk (MulAction.orbitRel G X) (ι a)
  have hc : Function.Injective c := by
    intro a b hab
    have h : (MulAction.orbitRel G X) (ι a) (ι b) := Quotient.exact hab
    rw [MulAction.orbitRel_apply] at h
    obtain ⟨g, hg⟩ := h
    exact (hinj b a ⟨g, hg⟩).symm
  have hout : ∀ a, ∃ g : G, g • ι a = (c a).out := by
    intro a
    have h : (MulAction.orbitRel G X) ((c a).out) (ι a) := Quotient.exact (Quotient.out_eq (c a))
    rw [MulAction.orbitRel_apply] at h
    exact h
  have hsupp : Function.support
      (fun o : MulAction.orbitRel.Quotient G X => if T o.out then φ o.out else 0) ⊆ Set.range c := by
    intro o ho
    have hTo : T o.out := by
      by_contra hn
      exact ho (if_neg hn)
    obtain ⟨a, g, hg⟩ := hsurj _ hTo
    refine ⟨a, ?_⟩
    rw [← Quotient.out_eq o]
    apply Quotient.sound
    have h : (MulAction.orbitRel G X) o.out (ι a) := by
      rw [MulAction.orbitRel_apply]
      exact ⟨g, hg⟩
    exact (MulAction.orbitRel G X).symm h
  rw [← hc.tsum_eq hsupp]
  refine tsum_congr fun a => ?_
  obtain ⟨g, hg⟩ := hout a
  rw [← hg, if_pos (hT g _ (hι a)), hφ g _ (hι a)]

theorem tsum_transversal_eq_tsum_orbitQuotient : ∀ {G X A : Type} [Group G] [MulAction G X] (ι : A → X) (T : X → Prop), (∀ g : G, ∀ x, T x → T (g • x)) → (∀ a, T (ι a)) → (∀ x, T x → ∃ a, ∃ g : G, g • ι a = x) → (∀ a b, (∃ g : G, g • ι a = ι b) → a = b) → (∀ φ : X → ℂ, (∀ g : G, ∀ x, T x → φ (g • x) = φ x) → ∑' a, φ (ι a) = ∑' o : MulAction.orbitRel.Quotient G X, if T o.out then φ o.out else 0) ∧ ∀ φ : X → ℝ≥0∞, (∀ g : G, ∀ x, T x → φ (g • x) = φ x) → ∑' a, φ (ι a) = ∑' o : MulAction.orbitRel.Quotient G X, if T o.out then φ o.out else 0 := by
  intro G X A _ _ ι T hT hι hsurj hinj
  exact ⟨fun φ hφ => tsum_transversal_eq_tsum_orbitQuotient_general ι T hT hι hsurj hinj φ hφ,
    fun φ hφ => tsum_transversal_eq_tsum_orbitQuotient_general ι T hT hι hsurj hinj φ hφ⟩

end GlobalTheory
