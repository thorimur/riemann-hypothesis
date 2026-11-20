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

open Matrix

namespace GlobalTheory.CompanionTheory.Transversal

theorem sum_add_eq_sum {X : Type} [AddCommGroup X] {M : Type} [AddCommGroup M]
    {A H : AddSubgroup X} {T : Finset X}
    (hTA : ∀ t ∈ T, t ∈ A) (hT : ∀ a ∈ A, ∃! t, t ∈ T ∧ a - t ∈ H)
    (F : X → M) (hF : ∀ a, ∀ h ∈ H, F (a + h) = F a) {a : X} (ha : a ∈ A) :
    ∑ t ∈ T, F (t + a) = ∑ t ∈ T, F t := by
  have hex : ∀ t ∈ T, ∃ s, s ∈ T ∧ (t + a) - s ∈ H := fun t ht =>
    (hT (t + a) (A.add_mem (hTA t ht) ha)).exists
  choose! φ hφT hφH using hex
  refine Finset.sum_bij (fun t _ => φ t) (fun t ht => hφT t ht) ?_ ?_ ?_
  · intro t₁ h₁ t₂ h₂ he
    have he' : φ t₁ = φ t₂ := he
    have hd : t₁ - t₂ ∈ H := by
      have := H.sub_mem (hφH t₁ h₁) (hφH t₂ h₂)
      rw [he'] at this
      have e : (t₁ + a - φ t₂) - (t₂ + a - φ t₂) = t₁ - t₂ := by abel
      rwa [e] at this
    have h0 : t₁ - t₁ ∈ H := by simp [H.zero_mem]
    exact (hT t₁ (hTA t₁ h₁)).unique ⟨h₁, h0⟩ ⟨h₂, hd⟩
  · intro s hs
    obtain ⟨t, ⟨ht, hd⟩, -⟩ := hT (s - a) (A.sub_mem (hTA s hs) ha)
    refine ⟨t, ht, ?_⟩
    have h1 : (t + a) - s ∈ H := by
      have := H.neg_mem hd
      have e : -(s - a - t) = t + a - s := by abel
      rwa [e] at this
    have h0 : (t + a) - (φ t) ∈ H := hφH t ht
    have hA : t + a ∈ A := A.add_mem (hTA t ht) ha
    exact (hT (t + a) hA).unique ⟨hφT t ht, h0⟩ ⟨hs, h1⟩
  · intro t ht
    have := hF (φ t) _ (hφH t ht)
    have e : φ t + (t + a - φ t) = t + a := by abel
    rwa [e] at this

theorem card_smul_sum_eq {X : Type} [AddCommGroup X] {M : Type} [AddCommGroup M] [Module ℂ M]
    {A H H' : AddSubgroup X} (hH : H ≤ A) (hH' : H' ≤ A) {T T' : Finset X}
    (hTA : ∀ t ∈ T, t ∈ A) (hT : ∀ a ∈ A, ∃! t, t ∈ T ∧ a - t ∈ H)
    (hTA' : ∀ t ∈ T', t ∈ A) (hT' : ∀ a ∈ A, ∃! t, t ∈ T' ∧ a - t ∈ H')
    (F : X → M) (hF : ∀ a, ∀ h ∈ H, F (a + h) = F a) (hF' : ∀ a, ∀ h ∈ H', F (a + h) = F a) :
    (T'.card : ℂ) • ∑ t ∈ T, F t = (T.card : ℂ) • ∑ t ∈ T', F t := by
  have h1 : ∑ t ∈ T, ∑ t' ∈ T', F (t + t') = T'.card • ∑ t ∈ T, F t := by
    rw [Finset.sum_comm, Finset.sum_congr rfl
      (fun t' ht' => sum_add_eq_sum hTA hT F hF (hTA' t' ht')), Finset.sum_const]
  have h2 : ∑ t ∈ T, ∑ t' ∈ T', F (t + t') = T.card • ∑ t ∈ T', F t := by
    have : ∀ t ∈ T, ∑ t' ∈ T', F (t + t') = ∑ t' ∈ T', F t' := fun t ht => by
      rw [← sum_add_eq_sum hTA' hT' F hF' (hTA t ht)]
      exact Finset.sum_congr rfl (fun t' _ => by rw [add_comm])
    rw [Finset.sum_congr rfl this, Finset.sum_const]
  rw [Nat.cast_smul_eq_nsmul, Nat.cast_smul_eq_nsmul, ← h1, h2]

end GlobalTheory.CompanionTheory.Transversal
