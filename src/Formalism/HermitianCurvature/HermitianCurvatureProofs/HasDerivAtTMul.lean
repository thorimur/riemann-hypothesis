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

open Set Filter Topology MeasureTheory intervalIntegral

namespace Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.Ann

noncomputable section

variable {ω : ℂ → ℂ →L[ℝ] ℝ} {S : Set ℂ} {w₀ : ℂ}

def prim (ω : ℂ → ℂ →L[ℝ] ℝ) (w₀ w : ℂ) : ℝ := ∫ t in (0 : ℝ)..1, ω (w₀ + (t : ℂ) * (w - w₀)) (w - w₀)

theorem hasDerivAt_t_mul (hω : ∀ p ∈ S, HasFDerivAt ω (fderiv ℝ ω p) p)
    (hsym : ∀ p ∈ S, ∀ h k : ℂ, fderiv ℝ ω p h k = fderiv ℝ ω p k h) {w : ℂ} {t : ℝ}
    (hγ : w₀ + (t : ℂ) * (w - w₀) ∈ S) (h : ℂ) :
    HasDerivAt (fun s : ℝ => s * ω (w₀ + (s : ℂ) * (w - w₀)) h)
      (ω (w₀ + (t : ℂ) * (w - w₀)) h + t * fderiv ℝ ω (w₀ + (t : ℂ) * (w - w₀)) h (w - w₀)) t := by
  have hγd : HasDerivAt (fun s : ℝ => w₀ + (s : ℂ) * (w - w₀)) (w - w₀) t := by
    have := ((Complex.ofRealCLM.hasDerivAt (x := t)).mul_const (w - w₀)).const_add w₀
    simpa using this
  have h1 : HasDerivAt (fun s : ℝ => ω (w₀ + (s : ℂ) * (w - w₀))) (fderiv ℝ ω (w₀ + (t : ℂ) * (w - w₀)) (w - w₀)) t :=
    (hω _ hγ).comp_hasDerivAt t hγd
  have h2 : HasDerivAt (fun s : ℝ => ω (w₀ + (s : ℂ) * (w - w₀)) h)
      (fderiv ℝ ω (w₀ + (t : ℂ) * (w - w₀)) (w - w₀) h) t := by
    exact (ContinuousLinearMap.apply ℝ ℝ h).hasFDerivAt.comp_hasDerivAt t h1
  have h3 := (hasDerivAt_id t).mul h2
  refine h3.congr_deriv ?_
  rw [hsym _ hγ h (w - w₀)]
  simp

end

end Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.Ann
