import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
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

theorem UpperTheory.Reformulated.B.Qh67.imag_of_sq :
    ∀ {c : ℂ} {d : ℕ},
    (0 : ℕ) < d → c ^ (2 : ℕ) = -(↑d : ℂ) → (starRingEnd ℂ : ℂ → ℂ) c = -c ∧ c ≠ (0 : ℂ) := by
  intro c d hd h
  have hd' : (0 : ℝ) < d := Nat.cast_pos.mpr hd
  have h1 : c.re * c.re - c.im * c.im = -(d : ℝ) := by
    have := congrArg Complex.re h
    simpa [pow_two] using this
  have h2 : c.re * c.im + c.im * c.re = 0 := by
    have := congrArg Complex.im h
    simpa [pow_two] using this
  have h3 : c.re * c.im = 0 := by linarith [mul_comm c.re c.im]
  have hre : c.re = 0 := by
    rcases mul_eq_zero.mp h3 with h4 | h4
    · exact h4
    · rw [h4] at h1
      nlinarith [mul_self_nonneg c.re]
  refine ⟨?_, ?_⟩
  · apply Complex.ext
    · simp [hre]
    · simp
  · rintro rfl
    simp at h1
    omega
