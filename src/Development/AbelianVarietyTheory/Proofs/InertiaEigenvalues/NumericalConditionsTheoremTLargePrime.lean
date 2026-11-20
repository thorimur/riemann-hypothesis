import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.Int.Star
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
open scoped PowerSeries Pointwise

namespace GlobalTheory

theorem numerical_bounds_of_forty_mul_lt : ∀ (l H N η r : ℕ), 2 ≤ N → 1 ≤ η → η < H → 4 * r ≤ N ^ 2 →
    40 * (H * N ^ 2 + N ^ 3) < l →
    2 * (H + η + 2 * (N - 1) * r + 1) + 2 < l ∧ 10 * H + 2 ≤ l ∧ 14 * H + (N + 2) * η < l ∧
      8 * H + 1 < l ∧ 4 * η * r + 4 < l ∧ (r + 2) * η < l + 1 := by
  intro l H N η r hN hη hηH hr hl
  have hN2 : 4 ≤ N ^ 2 := by nlinarith
  have hH : 2 ≤ H := by omega
  have hHN : 4 * H ≤ H * N ^ 2 := by nlinarith
  have hN3 : 8 ≤ N ^ 3 := by
    have : N ^ 3 = N * N ^ 2 := by ring
    nlinarith
  have hNr : 4 * (N * r) ≤ N ^ 3 := by
    have : N ^ 3 = N * N ^ 2 := by ring
    rw [this]; nlinarith
  have hsub : (N - 1) * r ≤ N * r := Nat.mul_le_mul_right _ (Nat.sub_le _ _)
  have hηr : 4 * (η * r) ≤ H * N ^ 2 := by
    have : η * r ≤ H * r := Nat.mul_le_mul_right _ hηH.le
    nlinarith
  have hNη : (N + 2) * η ≤ H * N ^ 2 := by
    have h1 : (N + 2) * η ≤ (N + 2) * H := Nat.mul_le_mul_left _ hηH.le
    have h2 : N + 2 ≤ N ^ 2 := by nlinarith
    have h3 : (N + 2) * H ≤ N ^ 2 * H := Nat.mul_le_mul_right _ h2
    nlinarith
  have hrη : r * η ≤ H * N ^ 2 := by
    have : r * η ≤ r * H := Nat.mul_le_mul_left _ hηH.le
    nlinarith
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · have : 2 * (N - 1) * r = 2 * ((N - 1) * r) := by ring
    rw [this]; nlinarith
  · nlinarith
  · nlinarith
  · nlinarith
  · have : 4 * η * r = 4 * (η * r) := by ring
    rw [this]; nlinarith
  · have : (r + 2) * η = r * η + 2 * η := by ring
    rw [this]; nlinarith

end GlobalTheory
