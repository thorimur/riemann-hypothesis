import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Matrix.Normed
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
import Mathlib.RingTheory.SimpleRing.Principal
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

namespace ReciprocityTheory.ChartRestriction.DS.S7

variable {n : ℕ}

section PathL
attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

lemma dga_exp (W : Matrix (Fin n) (Fin n) ℂ) :
    HasDerivAt (fun t : ℝ => NormedSpace.exp ((t : ℂ) • W)) W 0 := by
  have h := hasDerivAt_exp_smul_const (𝕂 := ℝ) W (0 : ℝ)
  simp only [zero_smul, NormedSpace.exp_zero, one_mul] at h
  have e : (fun t : ℝ => NormedSpace.exp ((t : ℂ) • W)) = fun u : ℝ => NormedSpace.exp (u • W) := by
    funext t
    rw [Complex.coe_smul]
  rw [e]
  exact h

lemma dga_path (Y z : Matrix (Fin n) (Fin n) ℂ) :
    HasDerivAt (fun t : ℝ => NormedSpace.exp (-((t : ℂ) • Y)) * z * NormedSpace.exp ((t : ℂ) • Y))
      (z * Y - Y * z) 0 := by
  have h1 : HasDerivAt (fun t : ℝ => NormedSpace.exp (-((t : ℂ) • Y))) (-Y) 0 := by
    have h := dga_exp (-Y)
    simpa [smul_neg] using h
  have h2 := dga_exp Y
  have e0 : NormedSpace.exp (((0 : ℝ) : ℂ) • Y) = 1 := by simp
  have e1 : NormedSpace.exp (-(((0 : ℝ) : ℂ) • Y)) = 1 := by simp
  have h3 := (h1.mul_const z).mul h2
  simp only [e0, e1, mul_one, one_mul] at h3
  have e2 : -Y * z + z * Y = z * Y - Y * z := by noncomm_ring
  rw [e2] at h3
  exact h3

end PathL

end ReciprocityTheory.ChartRestriction.DS.S7
