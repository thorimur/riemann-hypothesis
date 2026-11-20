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

namespace PI.SSU

open Complex

def coef (f : ℂ → ℂ) (n : ℤ) : ℂ :=
  ∫ x in (0:ℝ)..1, f x * Complex.exp (-(2 * (Real.pi : ℂ) * I * n * x))

def ShiftInv : Prop := ∀ f : ℂ → ℂ, Differentiable ℂ f → (∀ u, f (u + 1) = f u) →
  ∀ (w : ℂ) (n : ℤ),
    (∫ x in (0:ℝ)..1, f (x + w) * Complex.exp (-(2 * (Real.pi : ℂ) * I * n * (x + w)))) = coef f n

def Complete : Prop := ∀ f : ℂ → ℂ, Differentiable ℂ f → (∀ u, f (u + 1) = f u) →
  (∀ n, coef f n = 0) → f = 0

def KeyP : Prop := ∀ (f : ℂ → ℂ) (τ K : ℂ) (k : ℤ), Differentiable ℂ f → K ≠ 0 →
  (k = 1 ∨ k = -1) → (∀ u, f (u + 1) = f u) →
  (∀ u, f (u + τ) = K * Complex.exp (-(2 * (Real.pi : ℂ) * I * k * u)) * f u) → coef f 0 = 0 → f = 0

def FE (A ω p : ℂ) (F : ℂ → ℂ) : Prop := ∀ z, F (z + ω) * Complex.exp
    (-(Real.pi : ℂ) * z * (starRingEnd ℂ) ω / A - (Real.pi : ℂ) * ω * (starRingEnd ℂ) ω / (2 * A)) =
    p * F z

def normF (a A l : ℂ) (F : ℂ → ℂ) (u : ℂ) : ℂ :=
  F (a * u) * Complex.exp (-((Real.pi : ℂ) * (starRingEnd ℂ) a * a / (2 * A)) * u ^ 2 - l * u)

def cst (a b τ A l : ℂ) : ℂ :=
  -((Real.pi : ℂ) * (starRingEnd ℂ) a * a / (2 * A)) * τ ^ 2 - l * τ +
    (Real.pi : ℂ) * b * (starRingEnd ℂ) b / (2 * A)

end PI.SSU
