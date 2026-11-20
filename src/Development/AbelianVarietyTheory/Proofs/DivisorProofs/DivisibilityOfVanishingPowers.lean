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
import Mathlib.RingTheory.SimpleRing.Principal
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
open GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps GlobalTheory.DetInv Matrix TensorProduct

namespace GlobalTheory

theorem DetInv.dvd_pow_of_local_dvd_pow (R C ι : Type) [CommRing R] [Field C] (f : ι → (R →+* C)) (ξ : R)
    (hξ : ξ ∈ nonZeroDivisors R) (hf : ∀ i, f i ξ = 0) (hker : ∀ r : R, (∀ i, f i r = 0) → ξ ∣ r) :
    ∀ (n : ℕ) (r : R), (∀ i, ∃ s : R, f i s ≠ 0 ∧ ξ ^ n ∣ s * r) → ξ ^ n ∣ r := by
  intro n
  induction n with
  | zero => intro r _; simp
  | succ n ih =>
    intro r h
    have hr0 : ∀ i, f i r = 0 := by
      intro i
      obtain ⟨s, hs, t, ht⟩ := h i
      have h1 : f i (s * r) = 0 := by
        rw [ht, map_mul, map_pow, hf i, zero_pow (Nat.succ_ne_zero n), zero_mul]
      rw [map_mul] at h1
      exact (mul_eq_zero.mp h1).resolve_left hs
    obtain ⟨r1, rfl⟩ := hker r hr0
    have h2 : ∀ i, ∃ s : R, f i s ≠ 0 ∧ ξ ^ n ∣ s * r1 := by
      intro i
      obtain ⟨s, hs, t, ht⟩ := h i
      refine ⟨s, hs, t, ?_⟩
      have : ξ * (s * r1) = ξ * (ξ ^ n * t) := by
        rw [← mul_assoc, mul_comm ξ s, mul_assoc, ht]; ring
      exact (mul_cancel_left_mem_nonZeroDivisors hξ).mp this
    obtain ⟨u, hu⟩ := ih r1 h2
    exact ⟨u, by rw [hu]; ring⟩

example : ∀ (R C ι : Type) [CommRing R] [Field C] (f : ι → (R →+* C)) (ξ : R), ξ ∈ nonZeroDivisors R → (∀ i, f i ξ = 0) → (∀ r : R, (∀ i, f i r = 0) → ξ ∣ r) → ∀ (n : ℕ) (r : R), (∀ i, ∃ s : R, f i s ≠ 0 ∧ ξ ^ n ∣ s * r) → ξ ^ n ∣ r :=
  @DetInv.dvd_pow_of_local_dvd_pow

end GlobalTheory
