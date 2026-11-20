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

theorem UpperTheory.moderate_growth_add_smul :
    ∀ {Y : Type} (h : Y → ℝ) (f g : Y → ℂ) (z : ℂ), (∀ y, 1 ≤ h y) →
        (∃ (C : ℝ) (N : ℕ), ∀ y, ‖f y‖ ≤ C * h y ^ N) → (∃ (C : ℝ) (N : ℕ), ∀ y, ‖g y‖ ≤ C * h y ^ N) →
        ∃ (C : ℝ) (N : ℕ), ∀ y, ‖f y + z * g y‖ ≤ C * h y ^ N := by
  intro Y h f g z hh ⟨C, N, hf⟩ ⟨D, M, hg⟩
  refine ⟨|C| + ‖z‖ * |D|, N + M, fun y => ?_⟩
  have h0 : 0 ≤ h y := zero_le_one.trans (hh y)
  have h1 : ‖f y‖ ≤ |C| * h y ^ (N + M) :=
    (hf y).trans (mul_le_mul (le_abs_self C)
      (pow_le_pow_right₀ (hh y) (Nat.le_add_right N M)) (pow_nonneg h0 _) (abs_nonneg C))
  have h2 : ‖g y‖ ≤ |D| * h y ^ (N + M) :=
    (hg y).trans (mul_le_mul (le_abs_self D)
      (pow_le_pow_right₀ (hh y) (Nat.le_add_left M N)) (pow_nonneg h0 _) (abs_nonneg D))
  calc ‖f y + z * g y‖ ≤ ‖f y‖ + ‖z * g y‖ := norm_add_le _ _
    _ = ‖f y‖ + ‖z‖ * ‖g y‖ := by rw [norm_mul]
    _ ≤ |C| * h y ^ (N + M) + ‖z‖ * (|D| * h y ^ (N + M)) :=
        add_le_add h1 (mul_le_mul_of_nonneg_left h2 (norm_nonneg z))
    _ = (|C| + ‖z‖ * |D|) * h y ^ (N + M) := by ring
