import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Altitude
import Mathlib.MeasureTheory.Integral.Pi
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

universe u

namespace GlobalTheory.CompanionTheory.EisTube

theorem gaussInt : ∀ (ι : Type) [Fintype ι] (c : ℝ), 0 < c →
    MeasureTheory.Integrable (fun y : ι → ℝ => Real.exp (-(c * ∑ i, y i ^ 2))) := by
  intro ι _ c hc
  have h1 : MeasureTheory.Integrable (fun x : ℝ => Real.exp (-c * x ^ 2)) :=
    integrable_exp_neg_mul_sq hc
  have h2 := MeasureTheory.Integrable.fintype_prod (ι := ι) (f := fun _ x => Real.exp (-c * x ^ 2))
    (μ := fun _ => MeasureTheory.volume) (fun _ => h1)
  refine h2.congr (Filter.Eventually.of_forall fun y => ?_)
  simp only [← Real.exp_sum, Finset.mul_sum, Finset.sum_neg_distrib, neg_mul]

end GlobalTheory.CompanionTheory.EisTube
