import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.Circle
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

open MeasureTheory Matrix

namespace GlobalTheory.CompanionTheory.PsiShift

theorem integral_add_right_mul_char {K : Type*} [AddCommGroup K] [MeasurableSpace K]
    [MeasurableAdd K] (μ : Measure K) [μ.IsAddRightInvariant] (ψ : AddChar K Circle)
    (f : K → ℂ) (x : K) :
    ∫ y, f (y + x) * (ψ (-y) : ℂ) ∂μ = (ψ x : ℂ) * ∫ y, f y * (ψ (-y) : ℂ) ∂μ := by
  have h := integral_add_right_eq_self (μ := μ) (fun y => f y * (ψ (-(y - x)) : ℂ)) x
  have h1 : ∀ y, f (y + x) * (ψ (-(y + x - x)) : ℂ) = f (y + x) * (ψ (-y) : ℂ) := fun y => by
    simp
  have h2 : ∀ y, f y * (ψ (-(y - x)) : ℂ) = (ψ x : ℂ) * (f y * (ψ (-y) : ℂ)) := fun y => by
    have : -(y - x) = x + -y := by abel
    rw [this, AddChar.map_add_eq_mul]
    push_cast
    ring
  simp only [h1, h2] at h
  rw [h, integral_const_mul]

theorem vecMul_unipotent {R : Type*} [CommRing R] (h y x : R) :
    ![h, h * y] ᵥ* !![1, x; 0, 1] = ![h, h * (y + x)] := by
  ext i
  fin_cases i <;> simp [Matrix.vecMul, dotProduct, Fin.sum_univ_two] <;> ring

end GlobalTheory.CompanionTheory.PsiShift
