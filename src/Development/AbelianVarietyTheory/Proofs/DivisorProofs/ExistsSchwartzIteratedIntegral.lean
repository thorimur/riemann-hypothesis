import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Calculus.ParametricIntegral
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
import Mathlib.Topology.Sheaves.Init

open MeasureTheory

noncomputable section

namespace GlobalTheory.ConeSch

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]

theorem integral_curryLeft {α : Type} [MeasurableSpace α] (ν : Measure α) {n : ℕ}
    (F : α → ContinuousMultilinearMap ℝ (fun _ : Fin (n + 1) => V) ℂ) :
    ∫ a, (F a).curryLeft ∂ν = (∫ a, F a ∂ν).curryLeft :=
  (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (n + 1) => V) ℂ).toLinearIsometry.integral_comp_comm F

theorem hasFDerivAt_integral_curry {α : Type} [MeasurableSpace α] (ν : Measure α) {n : ℕ}
    (F : α → V → ContinuousMultilinearMap ℝ (fun _ : Fin n => V) ℂ)
    (F' : α → V → ContinuousMultilinearMap ℝ (fun _ : Fin (n + 1) => V) ℂ) (c : α → ℝ)
    (hF : ∀ a v, HasFDerivAt (F a) (F' a v).curryLeft v)
    (hFm : ∀ v, AEStronglyMeasurable (fun a => F a v) ν) (hFi : ∀ v, Integrable (fun a => F a v) ν)
    (hF'm : ∀ v, AEStronglyMeasurable (fun a => F' a v) ν) (hb : ∀ a v, ‖F' a v‖ ≤ c a)
    (hc : Integrable c ν) (v : V) :
    HasFDerivAt (fun w => ∫ a, F a w ∂ν) (∫ a, F' a v ∂ν).curryLeft v := by
  have h := hasFDerivAt_integral_of_dominated_of_fderiv_le (μ := ν) (F := fun w a => F a w)
    (F' := fun w a => (F' a w).curryLeft) (x₀ := v) (bound := c) (s := Set.univ) Filter.univ_mem
    (Filter.Eventually.of_forall fun w => hFm w) (hFi v)
    ((continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (n + 1) => V) ℂ).continuous.comp_aestronglyMeasurable (hF'm v))
    (ae_of_all _ fun a w _ => by simpa using hb a w) hc (ae_of_all _ fun a w _ => hF a w)
  rw [integral_curryLeft] at h
  exact h

end GlobalTheory.ConeSch
