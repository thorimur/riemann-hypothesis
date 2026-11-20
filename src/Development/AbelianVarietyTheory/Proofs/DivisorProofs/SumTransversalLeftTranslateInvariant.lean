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

namespace GlobalTheory

theorem sum_transversal_left_translate_invariant :
    ∀ {G X : Type} [Group G] [AddCommMonoid X] (H K : Subgroup G) (R : Finset G) (f : G → X),
      (∀ r ∈ R, r ∈ H) → (∀ k ∈ H, ∃! r, r ∈ R ∧ r⁻¹ * k ∈ K) →
      (∀ r ∈ H, ∀ c ∈ K, f (r * c) = f r) → ∀ k ∈ H, ∑ r ∈ R, f (k * r) = ∑ r ∈ R, f r := by
  intro G X _ _ H K R f hR hU hf k hk
  have hkH : ∀ a ∈ R, k * a ∈ H := fun a ha => H.mul_mem hk (hR a ha)
  refine Finset.sum_bij (fun a ha => Classical.choose (hU (k * a) (hkH a ha)).exists)
    (fun a ha => (Classical.choose_spec (hU (k * a) (hkH a ha)).exists).1) ?_ ?_ ?_
  · intro a₁ ha₁ a₂ ha₂ heq
    have h1 := (Classical.choose_spec (hU (k * a₁) (hkH a₁ ha₁)).exists).2
    have h2 := (Classical.choose_spec (hU (k * a₂) (hkH a₂ ha₂)).exists).2
    rw [heq] at h1
    set r' := Classical.choose (hU (k * a₂) (hkH a₂ ha₂)).exists
    have hm : a₁⁻¹ * a₂ ∈ K := by
      have := K.mul_mem (K.inv_mem h1) h2
      simpa [mul_assoc] using this
    have hu := (hU a₂ (hR a₂ ha₂)).unique (y₁ := a₁) (y₂ := a₂) ⟨ha₁, hm⟩ ⟨ha₂, by simpa using K.one_mem⟩
    exact hu
  · intro b hb
    have hb' : k⁻¹ * b ∈ H := H.mul_mem (H.inv_mem hk) (hR b hb)
    obtain ⟨a, ⟨ha, haK⟩, -⟩ := hU (k⁻¹ * b) hb'
    refine ⟨a, ha, ?_⟩
    have hs := Classical.choose_spec (hU (k * a) (hkH a ha)).exists
    have hbK : b⁻¹ * (k * a) ∈ K := by
      have := K.inv_mem haK
      simpa [mul_assoc] using this
    exact (hU (k * a) (hkH a ha)).unique hs ⟨hb, hbK⟩
  · intro a ha
    have hs := Classical.choose_spec (hU (k * a) (hkH a ha)).exists
    set r' := Classical.choose (hU (k * a) (hkH a ha)).exists
    have := hf r' (hR r' hs.1) (r'⁻¹ * (k * a)) hs.2
    rw [mul_inv_cancel_left] at this
    exact this

end GlobalTheory
