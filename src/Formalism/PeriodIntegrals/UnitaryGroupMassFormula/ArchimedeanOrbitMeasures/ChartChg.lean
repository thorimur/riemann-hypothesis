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
import Mathlib.Order.CompletePartialOrder
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

noncomputable section

namespace PI.AprimeInfW

open MeasureTheory Topology

theorem chart_change {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] (μ : Measure E) [μ.IsAddHaarMeasure] {Y : Type} [MeasurableSpace Y]
    (m : Measure Y) (χ : E → Y) (V : Set E) (f : E → ℝ)
    (hχ : ∀ S ⊆ V, MeasurableSet S → m (χ '' S) = ∫⁻ x in S, ENNReal.ofReal (f x) ∂μ)
    (ψ : E → E) (ψ' : E → E →L[ℝ] E) (U : Set E) (hψ : ∀ x ∈ U, HasFDerivWithinAt ψ (ψ' x) U x)
    (hinj : Set.InjOn ψ U) (hψV : ψ '' U ⊆ V) (A : Set E) (hAU : A ⊆ U) (hA : MeasurableSet A) :
    m ((χ ∘ ψ) '' A) = ∫⁻ p in A, ENNReal.ofReal (|(ψ' p).det| * f (ψ p)) ∂μ := by
  have hd : ∀ x ∈ A, HasFDerivWithinAt ψ (ψ' x) A x := fun x hx => (hψ x (hAU hx)).mono hAU
  have hinjA : Set.InjOn ψ A := hinj.mono hAU
  have hmeas : MeasurableSet (ψ '' A) := measurable_image_of_fderivWithin hA hd hinjA
  rw [Set.image_comp, hχ _ ((Set.image_mono hAU).trans hψV) hmeas,
    lintegral_image_eq_lintegral_abs_det_fderiv_mul μ hA hd hinjA]
  refine lintegral_congr fun p => ?_
  rw [ENNReal.ofReal_mul (abs_nonneg _)]

theorem chart_change_cont {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (f : E → ℝ) (ψ : E → E) (ψ' : E → E →L[ℝ] E) (x₀ : E) (hψ : ContinuousAt ψ x₀)
    (hf : ContinuousAt f (ψ x₀)) (hd : ContinuousAt (fun p => (ψ' p).det) x₀) :
    ContinuousAt (fun p => |(ψ' p).det| * f (ψ p)) x₀ := (continuous_abs.continuousAt.comp hd).mul (hf.comp hψ)

end PI.AprimeInfW
