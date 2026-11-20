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

open GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps GlobalTheory.DetInv Matrix TensorProduct

namespace GlobalTheory.DetInv

theorem dvd_of_twisted_eq :
    ∀ (R : Type) [CommRing R] (ψ : R →+* R) (m Δ Δs Δ' g b : R), m ∈ nonZeroDivisors R →
      Δ * Δs = m → Δ = g * ψ Δ → Δ' = g * b * ψ Δ' →
      (∀ z w : R, z * ψ m = m * w * ψ z → m ∣ z) → Δ ∣ Δ' := by
  intro R _ ψ m Δ Δs Δ' g b hm hmul hΔ hΔ' key
  have hz : (Δ' * Δs) * ψ m = m * b * ψ (Δ' * Δs) := by
    have h1 : Δ' * ψ Δ = b * ψ Δ' * Δ := by
      calc Δ' * ψ Δ = (g * b * ψ Δ') * ψ Δ := by rw [← hΔ']
        _ = b * ψ Δ' * (g * ψ Δ) := by ring
        _ = b * ψ Δ' * Δ := by rw [← hΔ]
    rw [← hmul, map_mul, map_mul]
    calc Δ' * Δs * (ψ Δ * ψ Δs) = (Δ' * ψ Δ) * (Δs * ψ Δs) := by ring
      _ = (b * ψ Δ' * Δ) * (Δs * ψ Δs) := by rw [h1]
      _ = Δ * Δs * b * (ψ Δ' * ψ Δs) := by ring
  obtain ⟨c, hc⟩ := key _ _ hz
  refine ⟨c, ?_⟩
  have hzero : (Δ' - Δ * c) * m = 0 := by
    have : (Δ' - Δ * c) * Δs = 0 := by
      rw [sub_mul, hc, ← hmul]; ring
    calc (Δ' - Δ * c) * m = ((Δ' - Δ * c) * Δs) * Δ := by rw [← hmul]; ring
      _ = 0 := by rw [this, zero_mul]
  exact sub_eq_zero.mp ((mem_nonZeroDivisors_iff_right.mp hm) _ hzero)

end GlobalTheory.DetInv
