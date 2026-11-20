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
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop

namespace GlobalTheory.CompanionTheory.Strip

theorem strip_open_real_discs (n : ℕ) (X : Fin n → ℝ) :
    IsOpen {z : ℂ | ∀ j, |z.im * X j| < Real.pi / 4} ∧
    (∀ t : ℝ, (t : ℂ) ∈ {z : ℂ | ∀ j, |z.im * X j| < Real.pi / 4}) ∧
    ∀ z ∈ {z : ℂ | ∀ j, |z.im * X j| < Real.pi / 4}, ∃ (t ρ : ℝ), 0 < ρ ∧
      z ∈ Metric.ball (t : ℂ) ρ ∧
      Metric.ball (t : ℂ) ρ ⊆ {z : ℂ | ∀ j, |z.im * X j| < Real.pi / 4} := by
  set S := {z : ℂ | ∀ j, |z.im * X j| < Real.pi / 4} with hS
  have hpi : 0 < Real.pi / 4 := by positivity
  refine ⟨?_, ?_, ?_⟩
  · have h : S = ⋂ j, {z : ℂ | |z.im * X j| < Real.pi / 4} := by
      ext z
      simp [hS]
    rw [h]
    exact isOpen_iInter_of_finite fun j => isOpen_lt (by fun_prop) continuous_const
  · intro t
    simp [hS, hpi]
  · intro z hz
    have hopen : IsOpen {r : ℝ | ∀ j, r * |X j| < Real.pi / 4} := by
      have h : {r : ℝ | ∀ j, r * |X j| < Real.pi / 4} = ⋂ j, {r : ℝ | r * |X j| < Real.pi / 4} := by
        ext r
        simp
      rw [h]
      exact isOpen_iInter_of_finite fun j => isOpen_lt (by fun_prop) continuous_const
    have hmem : |z.im| ∈ {r : ℝ | ∀ j, r * |X j| < Real.pi / 4} := by
      intro j
      have h := hz j
      rwa [abs_mul] at h
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hopen _ hmem
    refine ⟨z.re, |z.im| + ε / 2, by positivity, ?_, ?_⟩
    · rw [Metric.mem_ball, Complex.dist_eq]
      have h : z - (z.re : ℂ) = (z.im : ℂ) * Complex.I := by
        apply Complex.ext <;> simp
      rw [h, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs]
      linarith
    · intro w hw j
      rw [Metric.mem_ball, Complex.dist_eq] at hw
      have him : |w.im| < |z.im| + ε / 2 := by
        have h1 : |(w - (z.re : ℂ)).im| ≤ ‖w - (z.re : ℂ)‖ := Complex.abs_im_le_norm _
        simp only [Complex.sub_im, Complex.ofReal_im, sub_zero] at h1
        linarith
      have hρ : (|z.im| + ε / 2) * |X j| < Real.pi / 4 := by
        have hin : |z.im| + ε / 2 ∈ Metric.ball |z.im| ε := by
          rw [Metric.mem_ball, Real.dist_eq, show |z.im| + ε / 2 - |z.im| = ε / 2 by ring,
            abs_of_pos (by positivity)]
          linarith
        exact hball hin j
      show |w.im * X j| < Real.pi / 4
      rw [abs_mul]
      calc |w.im| * |X j| ≤ (|z.im| + ε / 2) * |X j| :=
            mul_le_mul_of_nonneg_right him.le (abs_nonneg _)
        _ < Real.pi / 4 := hρ

end GlobalTheory.CompanionTheory.Strip
