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
import Mathlib.Tactic.ENatToNat
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
import Mathlib.Topology.Sheaves.Presheaf
open MeasureTheory Filter Topology
open scoped ENNReal

namespace GlobalTheory.CompanionTheory.Dblock

theorem lintegral_enorm_sq_le {α : Type} [MeasurableSpace α] (μ : Measure α) (g : α → ℝ≥0∞)
    (hg : AEMeasurable g μ) :
    (∫⁻ x, g x ∂μ) ^ 2 ≤ μ Set.univ * ∫⁻ x, g x ^ 2 ∂μ := by
  have h := ENNReal.lintegral_mul_le_Lp_mul_Lq μ Real.HolderConjugate.two_two hg
    (aemeasurable_const (b := (1 : ℝ≥0∞)))
  have h1 : (∫⁻ a, ((g * fun _ => (1 : ℝ≥0∞)) : α → ℝ≥0∞) a ∂μ) = ∫⁻ x, g x ∂μ := by simp
  have h2 : (∫⁻ _a, (1 : ℝ≥0∞) ^ (2 : ℝ) ∂μ) = μ Set.univ := by simp
  have h3 : (∫⁻ a, g a ^ (2 : ℝ) ∂μ) = ∫⁻ x, g x ^ 2 ∂μ := by
    refine lintegral_congr fun x => ?_
    exact ENNReal.rpow_two _
  rw [h1, h2, h3] at h
  calc (∫⁻ x, g x ∂μ) ^ 2
      ≤ ((∫⁻ x, g x ^ 2 ∂μ) ^ (1 / (2 : ℝ)) * (μ Set.univ) ^ (1 / (2 : ℝ))) ^ 2 := by
        gcongr
    _ = μ Set.univ * ∫⁻ x, g x ^ 2 ∂μ := by
        rw [mul_pow, ← ENNReal.rpow_natCast, ← ENNReal.rpow_natCast, ← ENNReal.rpow_mul,
          ← ENNReal.rpow_mul]
        norm_num
        rw [mul_comm]

theorem enorm_mean_sq_mul_le {α : Type} [MeasurableSpace α] (ν : Measure α) (s : Set α)
    (f : α → ℂ) :
    ‖((ν.real s : ℝ) : ℂ)⁻¹ * ∫ x in s, f x ∂ν‖ₑ ^ 2 * ν s ≤ ∫⁻ x in s, ‖f x‖ₑ ^ 2 ∂ν := by
  by_cases h0 : ν s = 0
  · simp [h0]
  by_cases htop : ν s = ⊤
  · simp [Measure.real, htop]
  by_cases hf : IntegrableOn f s ν
  · have hcs := lintegral_enorm_sq_le (ν.restrict s) (fun x => ‖f x‖ₑ) hf.1.enorm
    rw [Measure.restrict_apply_univ] at hcs
    have hz : ‖∫ x in s, f x ∂ν‖ₑ ≤ ∫⁻ x in s, ‖f x‖ₑ ∂ν := enorm_integral_le_lintegral_enorm _
    have hc : ‖((ν.real s : ℝ) : ℂ)⁻¹‖ₑ = (ν s)⁻¹ := by
      have hne : ((ν.real s : ℝ) : ℂ) ≠ 0 := by
        simp [Measure.real, ENNReal.toReal_eq_zero_iff, h0, htop]
      rw [enorm_inv hne]
      congr 1
      rw [← ofReal_norm_eq_enorm, Complex.norm_real, Real.norm_of_nonneg measureReal_nonneg,
        Measure.real, ENNReal.ofReal_toReal htop]
    rw [enorm_mul, hc]
    calc ((ν s)⁻¹ * ‖∫ x in s, f x ∂ν‖ₑ) ^ 2 * ν s
        ≤ ((ν s)⁻¹ * ∫⁻ x in s, ‖f x‖ₑ ∂ν) ^ 2 * ν s := by gcongr
      _ = ((ν s)⁻¹) ^ 2 * (∫⁻ x in s, ‖f x‖ₑ ∂ν) ^ 2 * ν s := by rw [mul_pow]
      _ ≤ ((ν s)⁻¹) ^ 2 * (ν s * ∫⁻ x in s, ‖f x‖ₑ ^ 2 ∂ν) * ν s := by gcongr
      _ = ((ν s)⁻¹ * ν s) ^ 2 * ∫⁻ x in s, ‖f x‖ₑ ^ 2 ∂ν := by ring
      _ = ∫⁻ x in s, ‖f x‖ₑ ^ 2 ∂ν := by
        rw [ENNReal.inv_mul_cancel h0 htop]; simp
  · rw [integral_undef hf]
    simp

end GlobalTheory.CompanionTheory.Dblock
