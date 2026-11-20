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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

namespace PI.EF.PK

open Complex MeasureTheory intervalIntegral Real

lemma vert_inv_right (c d b : ℝ) (w : ℂ) (hb : w.re < b) :
    I • ∫ y : ℝ in c..d, 1 / (((b : ℂ) + y * I) - w) =
      Complex.log (((b : ℂ) + d * I) - w) - Complex.log (((b : ℂ) + c * I) - w) := by
  have hz : ∀ y : ℝ, ((b : ℂ) + y * I - w) ∈ Complex.slitPlane := fun y => by
    rw [Complex.mem_slitPlane_iff]
    left
    simp only [Complex.sub_re, Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, mul_zero, mul_one, sub_zero, add_zero]
    linarith
  have hne : ∀ y : ℝ, ((b : ℂ) + y * I - w) ≠ 0 := fun y => Complex.slitPlane_ne_zero (hz y)
  have hd : ∀ y : ℝ, HasDerivAt (fun y : ℝ => Complex.log ((b : ℂ) + y * I - w))
      (I * (1 / ((b : ℂ) + y * I - w))) y := by
    intro y
    have h1 : HasDerivAt (fun y : ℝ => (b : ℂ) + y * I - w) I y := by
      simpa using (((hasDerivAt_id y).ofReal_comp.mul_const I).const_add (b : ℂ)).sub_const w
    have h2 := h1.clog_real (hz y)
    convert h2 using 1
    rw [one_div, div_eq_mul_inv]
  rw [smul_eq_mul, ← intervalIntegral.integral_const_mul,
    intervalIntegral.integral_eq_sub_of_hasDerivAt (fun y _ => hd y)]
  exact (continuous_const.mul (continuous_const.div (by fun_prop) hne)).intervalIntegrable _ _

end PI.EF.PK
