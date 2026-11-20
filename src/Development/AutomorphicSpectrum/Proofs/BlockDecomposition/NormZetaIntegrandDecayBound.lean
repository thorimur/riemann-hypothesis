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
import Mathlib.Tactic.ENatToNat
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
open NumberField IsDedekindDomain MeasureTheory Matrix Filter Topology
open GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.GodementSection (localChar)
open GroundTheory.Automorphic.Reduction (finAt infAt maxCompact)
open GroundTheory.Automorphic.GLnLocal (integralGL)
open GroundTheory.Global.AdicLiesOver
open Ad3 Ad3.K Ad3.K.QuadraticBaseChangeGL3
open Ad3.R (G2 Jd md KA lc)
open scoped NumberField.AdeleRing ValuativeRel
open GlobalTheory.CompanionTheory.GL2Factorization

namespace GlobalTheory.CompanionTheory.GL2Factorization

theorem real_integrand_norm_le_ptw : ∀ (x₃ x₂ s : ℂ) (A B C m : ℝ) (T N : ℕ), 0 < A → 0 < B → ‖x₃‖ ≤ C / (A * B) ^ T / ((1 + A) * (1 + B)) ^ N → ‖x₂‖ ≤ A ^ m → ‖x₃ * x₂ * ((A : ℂ) ^ (s - 3 / 2)) * ((B : ℂ) ^ (2 * s - 1))‖ ≤ C * (A ^ (s.re - 3 / 2 + m - T) * (1 + A) ^ (-(N : ℝ))) * (B ^ (2 * s.re - 1 - T) * (1 + B) ^ (-(N : ℝ))) := by
  intro x₃ x₂ s A B C m T N hA hB h3 h2
  have hA1 : 0 < 1 + A := by linarith
  have hB1 : 0 < 1 + B := by linarith
  have e1 : ‖(A : ℂ) ^ (s - 3 / 2)‖ = A ^ (s.re - 3 / 2) := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hA]
    simp
  have e2 : ‖(B : ℂ) ^ (2 * s - 1)‖ = B ^ (2 * s.re - 1) := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hB]
    simp
  have key : ‖x₃‖ * ‖x₂‖ ≤ (C / (A * B) ^ T / ((1 + A) * (1 + B)) ^ N) * A ^ m :=
    mul_le_mul h3 h2 (norm_nonneg _) ((norm_nonneg _).trans h3)
  have hP : 0 ≤ A ^ (s.re - 3 / 2) * B ^ (2 * s.re - 1) :=
    mul_nonneg (Real.rpow_nonneg hA.le _) (Real.rpow_nonneg hB.le _)
  have hR : C * (A ^ (s.re - 3 / 2 + m - T) * (1 + A) ^ (-(N : ℝ))) *
      (B ^ (2 * s.re - 1 - T) * (1 + B) ^ (-(N : ℝ))) =
      (C / (A * B) ^ T / ((1 + A) * (1 + B)) ^ N) * A ^ m *
        (A ^ (s.re - 3 / 2) * B ^ (2 * s.re - 1)) := by
    rw [Real.rpow_sub hA, Real.rpow_add hA, Real.rpow_sub hB, Real.rpow_neg hA1.le,
      Real.rpow_neg hB1.le, Real.rpow_natCast, Real.rpow_natCast, Real.rpow_natCast,
      Real.rpow_natCast, mul_pow, mul_pow]
    field_simp
  rw [norm_mul, norm_mul, norm_mul, e1, e2, hR, mul_assoc (‖x₃‖ * ‖x₂‖)]
  exact mul_le_mul_of_nonneg_right key hP

end GlobalTheory.CompanionTheory.GL2Factorization
