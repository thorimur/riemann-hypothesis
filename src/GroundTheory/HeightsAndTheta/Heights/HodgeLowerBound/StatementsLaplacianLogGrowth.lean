import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.InnerProductSpace.Laplacian
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
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open InnerProductSpace Laplacian Real

def LaplacianLogGrowth.Statement : Prop :=
  ∀ (u F : ℂ → ℝ) (a r : ℝ), ContDiff ℝ 2 u → 0 < r → ContDiffOn ℝ 2 F (Metric.ball 0 r) →
    (∀ y : ℂ, r⁻¹ < ‖y‖ → u y = a * Real.log ‖y‖ + F y⁻¹) →
    MeasureTheory.Integrable (Δ u) ∧ ∫ y, Δ u y = 2 * π * a

def fsPotPlane (y : ℂ) : ℝ := Real.log (1 + ‖y‖ ^ 2) / 2

theorem contDiff_fsPotPlane : ContDiff ℝ 2 fsPotPlane := by
  unfold fsPotPlane
  exact ((contDiff_const.add (contDiff_norm_sq ℝ)).log fun y => by positivity).div_const _

theorem fsPotPlane_eq {y : ℂ} (hy : 1⁻¹ < ‖y‖) : fsPotPlane y = 1 * Real.log ‖y‖ + fsPotPlane y⁻¹ := by
  have hy0 : 0 < ‖y‖ := lt_trans (by norm_num) hy
  unfold fsPotPlane
  rw [norm_inv]
  have h1 : 1 + ‖y‖ ^ 2 = ‖y‖ ^ 2 * (1 + ‖y‖⁻¹ ^ 2) := by
    field_simp
    ring
  rw [h1, Real.log_mul (by positivity) (by positivity), Real.log_pow]
  push_cast
  ring

end GroundTheory.Heights₂.Heights.LowerBoundFree
