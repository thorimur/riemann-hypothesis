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

namespace ReciprocityTheory.GeometryOfNumbersTheory

open Matrix MeasureTheory Complex

theorem morseGen_ident (fz qz : ℂ) (φz φ0 νz ν0 : ℝ) (n : ℕ) :
    ‖fz * cexp (-(n : ℂ) * qz / 2)‖ ^ 2 * Real.exp (-((n : ℝ) * (φz - φ0 - qz.re))) * (νz / ν0) =
      ‖fz‖ ^ 2 * Real.exp (-((n : ℝ) * φz)) * νz * (Real.exp ((n : ℝ) * φ0) / ν0) := by
  have hre : (-(n : ℂ) * qz / 2).re = -((n : ℝ) * qz.re) / 2 := by simp
  have e1 : Real.exp (-((n : ℝ) * qz.re) / 2) ^ 2 * Real.exp (-((n : ℝ) * (φz - φ0 - qz.re))) =
      Real.exp (-((n : ℝ) * φz)) * Real.exp ((n : ℝ) * φ0) := by
    rw [sq, ← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
    congr 1
    ring
  rw [norm_mul, Complex.norm_exp, hre, mul_pow]
  calc ‖fz‖ ^ 2 * Real.exp (-((n : ℝ) * qz.re) / 2) ^ 2 * Real.exp (-((n : ℝ) * (φz - φ0 - qz.re)))
        * (νz / ν0)
      = ‖fz‖ ^ 2 * (Real.exp (-((n : ℝ) * qz.re) / 2) ^ 2 *
          Real.exp (-((n : ℝ) * (φz - φ0 - qz.re)))) * (νz / ν0) := by ring
    _ = _ := by rw [e1]; ring

theorem morseGen_sq_le_sum {D : ℕ} (z : Fin D → ℂ) : ‖z‖ ^ 2 ≤ ∑ j, ‖z j‖ ^ 2 := by
  have hs : 0 ≤ ∑ j, ‖z j‖ ^ 2 := Finset.sum_nonneg fun j _ => by positivity
  have h : ‖z‖ ≤ Real.sqrt (∑ j, ‖z j‖ ^ 2) := by
    refine (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).2 fun i => ?_
    apply Real.le_sqrt_of_sq_le
    exact Finset.single_le_sum (f := fun j => ‖z j‖ ^ 2) (fun j _ => by positivity)
      (Finset.mem_univ i)
  calc ‖z‖ ^ 2 ≤ Real.sqrt (∑ j, ‖z j‖ ^ 2) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h 2
    _ = _ := Real.sq_sqrt hs

theorem morseGen_levi_le {D : ℕ} (B : (Fin D → ℂ) →L[ℝ] (Fin D → ℂ) →L[ℝ] ℝ) (z : Fin D → ℂ) :
    (B z z + B (I • z) (I • z)) / 4 ≤ ‖B‖ / 2 * ‖z‖ ^ 2 := by
  have h1 : B z z ≤ ‖B‖ * ‖z‖ * ‖z‖ := (le_abs_self _).trans (B.le_opNorm₂ z z)
  have h2 : B (I • z) (I • z) ≤ ‖B‖ * ‖I • z‖ * ‖I • z‖ :=
    (le_abs_self _).trans (B.le_opNorm₂ _ _)
  have hI : ‖I • z‖ = ‖z‖ := by rw [norm_smul, Complex.norm_I, one_mul]
  rw [hI] at h2
  nlinarith

end ReciprocityTheory.GeometryOfNumbersTheory
