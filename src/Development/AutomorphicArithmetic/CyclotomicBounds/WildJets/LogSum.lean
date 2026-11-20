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
import Mathlib.Tactic.Monotonicity.Lemmas
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

theorem UpperTheory.WildA.logSum :
    ∀ y : ℝ, 1 ≤ y → ∑ l ∈ (Finset.range (⌊y⌋₊ + 1)).filter Nat.Prime, Real.logb l y * Real.log l ≤ y * Real.log y := by
  intro y hy
  set S := (Finset.range (⌊y⌋₊ + 1)).filter Nat.Prime with hS
  have hlogy : 0 ≤ Real.log y := Real.log_nonneg hy
  have hterm : ∀ l ∈ S, Real.logb l y * Real.log l = Real.log y := by
    intro l hl
    have hp : Nat.Prime l := (Finset.mem_filter.1 hl).2
    have h1 : (1:ℝ) < l := by exact_mod_cast hp.one_lt
    have hlog : Real.log l ≠ 0 := (Real.log_pos h1).ne'
    rw [Real.logb, div_mul_cancel₀ _ hlog]
  rw [Finset.sum_congr rfl hterm, Finset.sum_const, nsmul_eq_mul]
  apply mul_le_mul_of_nonneg_right _ hlogy
  have hsub : S ⊆ (Finset.range (⌊y⌋₊ + 1)).erase 0 := by
    intro l hl
    rw [hS, Finset.mem_filter] at hl
    exact Finset.mem_erase.2 ⟨hl.2.ne_zero, hl.1⟩
  have hcard := Finset.card_le_card hsub
  rw [Finset.card_erase_of_mem (by simp), Finset.card_range] at hcard
  have h2 : S.card ≤ ⌊y⌋₊ := by omega
  calc (S.card : ℝ) ≤ (⌊y⌋₊ : ℝ) := by exact_mod_cast h2
    _ ≤ y := Nat.floor_le (by linarith)
