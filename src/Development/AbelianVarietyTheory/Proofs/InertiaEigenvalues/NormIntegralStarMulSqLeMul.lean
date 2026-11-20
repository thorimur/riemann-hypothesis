import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Altitude
import Mathlib.MeasureTheory.Function.L2Space
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
open MeasureTheory

namespace GlobalTheory

theorem norm_integral_star_mul_sq_le {X : Type} [MeasurableSpace X] (μ : Measure X) (f h : X → ℂ)
    (hf : AEStronglyMeasurable f μ) (hh : AEStronglyMeasurable h μ)
    (hff : Integrable (fun x => star (f x) * f x) μ) (hhh : Integrable (fun x => star (h x) * h x) μ) :
    ‖∫ x, star (f x) * h x ∂μ‖ ^ 2 ≤ (∫ x, star (f x) * f x ∂μ).re * (∫ x, star (h x) * h x ∂μ).re := by
  have key : ∀ g : X → ℂ, (fun x => star (g x) * g x) = fun x => ((‖g x‖ ^ 2 : ℝ) : ℂ) := by
    intro g; funext x; rw [Complex.star_def, Complex.conj_mul']; push_cast; rfl
  have re_eq : ∀ g : X → ℂ, (∫ x, star (g x) * g x ∂μ).re = ∫ x, ‖g x‖ ^ 2 ∂μ := by
    intro g; rw [key g, integral_complex_ofReal]; rfl
  have int_sq : ∀ g : X → ℂ, Integrable (fun x => star (g x) * g x) μ → Integrable (fun x => ‖g x‖ ^ 2) μ := by
    intro g hg; rw [key g] at hg; have hr := hg.re; simp only [RCLike.re_to_complex, Complex.ofReal_re] at hr; exact hr
  have mf : MemLp f (ENNReal.ofReal 2) μ := by
    rw [show ENNReal.ofReal 2 = 2 by simp]; exact (memLp_two_iff_integrable_sq_norm hf).mpr (int_sq f hff)
  have mh : MemLp h (ENNReal.ofReal 2) μ := by
    rw [show ENNReal.ofReal 2 = 2 by simp]; exact (memLp_two_iff_integrable_sq_norm hh).mpr (int_sq h hhh)
  have hold := integral_mul_norm_le_Lp_mul_Lq (p := 2) (q := 2) Real.HolderConjugate.two_two mf mh
  simp only [Real.rpow_two] at hold
  rw [re_eq f, re_eq h]
  have A0 : 0 ≤ ∫ x, ‖f x‖ ^ 2 ∂μ := integral_nonneg fun x => by positivity
  have B0 : 0 ≤ ∫ x, ‖h x‖ ^ 2 ∂μ := integral_nonneg fun x => by positivity
  have n1 : ‖∫ x, star (f x) * h x ∂μ‖ ≤ ∫ x, ‖f x‖ * ‖h x‖ ∂μ := by
    refine (norm_integral_le_integral_norm _).trans (le_of_eq ?_)
    congr 1; funext x; rw [norm_mul, norm_star]
  have n0 : 0 ≤ ‖∫ x, star (f x) * h x ∂μ‖ := norm_nonneg _
  have hsq : ((∫ x, ‖f x‖ ^ 2 ∂μ) ^ (1 / (2:ℝ)) * (∫ x, ‖h x‖ ^ 2 ∂μ) ^ (1 / (2:ℝ))) ^ 2
      = (∫ x, ‖f x‖ ^ 2 ∂μ) * (∫ x, ‖h x‖ ^ 2 ∂μ) := by
    rw [mul_pow, ← Real.sqrt_eq_rpow, ← Real.sqrt_eq_rpow, Real.sq_sqrt A0, Real.sq_sqrt B0]
  calc ‖∫ x, star (f x) * h x ∂μ‖ ^ 2 ≤ ((∫ x, ‖f x‖ ^ 2 ∂μ) ^ (1 / (2:ℝ)) * (∫ x, ‖h x‖ ^ 2 ∂μ) ^ (1 / (2:ℝ))) ^ 2 :=
        pow_le_pow_left₀ n0 (n1.trans hold) 2
    _ = _ := hsq

end GlobalTheory
