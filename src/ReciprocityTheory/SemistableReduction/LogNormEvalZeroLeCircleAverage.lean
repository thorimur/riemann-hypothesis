import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Complex.JensenFormula
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

noncomputable section

namespace ReciprocityTheory.MultiplicativeHeights

open Polynomial

theorem log_norm_eval_zero_le_circleAverage (q : ℂ[X]) (hq : q.eval 0 ≠ 0) :
    Real.log ‖q.eval 0‖ ≤ Real.circleAverage (fun ζ => Real.log ‖q.eval ζ‖) 0 1 := by
  have hA : AnalyticOnNhd ℂ (fun z => q.eval z) Set.univ := fun z _ =>
    (Polynomial.differentiable q).analyticAt z
  have hM : MeromorphicOn (fun z => q.eval z) (Metric.closedBall (0 : ℂ) |(1 : ℝ)|) :=
    (hA.mono (Set.subset_univ _)).meromorphicOn
  have hD : 0 ≤ MeromorphicOn.divisor (fun z => q.eval z) (Metric.closedBall (0 : ℂ) |(1 : ℝ)|) :=
    MeromorphicOn.AnalyticOnNhd.divisor_nonneg (hA.mono (Set.subset_univ _))
  rw [MeromorphicOn.circleAverage_log_norm one_ne_zero hM,
    AnalyticAt.meromorphicTrailingCoeffAt_of_ne_zero (hA 0 trivial) hq, Real.log_one, mul_zero,
    add_zero]
  have hsum : 0 ≤ ∑ᶠ u, ((MeromorphicOn.divisor (fun z => q.eval z)
      (Metric.closedBall (0 : ℂ) |(1 : ℝ)|) u : ℤ) : ℝ) * Real.log (1 * ‖0 - u‖⁻¹) := by
    apply finsum_nonneg
    intro u
    by_cases hu : u ∈ Metric.closedBall (0 : ℂ) |(1 : ℝ)|
    · have hle : ‖u‖ ≤ 1 := by simpa using hu
      apply mul_nonneg
      · exact_mod_cast (show (0 : ℤ) ≤ _ by simpa using hD u)
      · rw [one_mul, Real.log_inv, zero_sub, norm_neg]
        exact neg_nonneg.mpr (Real.log_nonpos (norm_nonneg _) hle)
    · have h0 : MeromorphicOn.divisor (fun z => q.eval z) (Metric.closedBall (0 : ℂ) |(1 : ℝ)|) u = 0 := by
        by_contra h
        exact hu (Function.locallyFinsuppWithin.supportWithinDomain _ (Function.mem_support.mpr h))
      simp [h0]
  linarith

def lineRestrict {σ : Type*} (f : MvPolynomial σ ℂ) (x y : σ → ℂ) : ℂ[X] :=
  MvPolynomial.aeval (fun i => C (x i) + C (y i) * X) f

theorem eval_smul_of_isHomogeneous {σ : Type*} {f : MvPolynomial σ ℂ} {a : ℕ}
    (hf : f.IsHomogeneous a) (c : ℂ) (x : σ → ℂ) :
    MvPolynomial.eval (fun i => c * x i) f = c ^ a * MvPolynomial.eval x f := by
  classical
  rw [MvPolynomial.eval_eq, MvPolynomial.eval_eq, Finset.mul_sum]
  refine Finset.sum_congr rfl fun d hd => ?_
  have hdeg : ∑ i ∈ d.support, d i = a := by
    have h := hf (MvPolynomial.mem_support_iff.mp hd)
    simpa [Finsupp.weight_apply, Finsupp.sum] using h
  simp_rw [mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, hdeg]
  ring

end ReciprocityTheory.MultiplicativeHeights
