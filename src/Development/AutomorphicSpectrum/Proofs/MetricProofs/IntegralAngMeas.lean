import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.Poisson
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.InnerProductSpace.Harmonic.Basic
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

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.Flat

open MeasureTheory Real

def punct {n : ℕ} (R : ℝ) : Set (Fin n → ℂ) := {z | ∀ i, z i ≠ 0 ∧ ‖z i‖ < R}

def pker (ρ : ℝ) (w : ℂ) (t : ℝ) : ℝ := poissonKernel 0 w (circleMap 0 ρ t)

def angMeas : Measure ℝ := ENNReal.ofReal (2 * π)⁻¹ • volume.restrict (Set.Ioc 0 (2 * π))

instance : IsProbabilityMeasure angMeas := ⟨by
  have h : (0 : ℝ) < 2 * π := by positivity
  simp only [angMeas, Measure.smul_apply, Measure.restrict_apply, MeasurableSet.univ,
    Set.univ_inter, Real.volume_Ioc, sub_zero, smul_eq_mul]
  rw [← ENNReal.ofReal_mul (by positivity), inv_mul_cancel₀ h.ne', ENNReal.ofReal_one]⟩

theorem integral_angMeas (F : ℂ → ℝ) (ρ : ℝ) :
    ∫ t, F (circleMap 0 ρ t) ∂angMeas = Real.circleAverage F 0 ρ := by
  have h : (0 : ℝ) < 2 * π := by positivity
  rw [angMeas, integral_smul_measure, Real.circleAverage_def,
    intervalIntegral.integral_of_le h.le, ENNReal.toReal_ofReal (by positivity)]

def torusPt {n : ℕ} (ρ : ℝ) (θ : Fin n → ℝ) : Fin n → ℂ := fun i => circleMap 0 ρ (θ i)

def polyPoisson {n : ℕ} (ρ : ℝ) (h : (Fin n → ℂ) → ℝ) (z : Fin n → ℂ) : ℝ :=
  ∫ θ, (∏ i, pker ρ (z i) (θ i)) * h (torusPt ρ θ) ∂(Measure.pi fun _ : Fin n => angMeas)

def SepHarm {n : ℕ} (R : ℝ) (f : (Fin n → ℂ) → ℝ) : Prop :=
  ∀ z ∈ punct R, ∀ i, InnerProductSpace.HarmonicAt (fun t : ℂ => f (Function.update z i t)) (z i)

end GlobalTheory.CompanionTheory.Ar.PB.Flat
