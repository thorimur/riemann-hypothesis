import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Interval.Basic
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

namespace ReciprocityTheory.ChartRestriction.G.AI

open intervalIntegral

def ArithmeticIntersectionKernelFirst : Prop :=
  ∫ s in (0 : ℝ)..1, Real.log s = -1

def ArithmeticIntersectionKernelSecond : Prop :=
  (1 / 2 : ℝ) * (∫ t in (-1 : ℝ)..1, Real.log ((1 - t) / 2)) = -1 ∧
  (1 / 2 : ℝ) * (∫ t in (-1 : ℝ)..1, t * Real.log ((1 - t) / 2)) = -1 / 2 ∧
  -(1 / 2 : ℝ) * (2 * ((1 / 2 : ℝ) * ∫ t in (-1 : ℝ)..1, Real.log ((1 - t) / 2)) -
      (4 / 3) * ((1 / 2 : ℝ) * ∫ t in (-1 : ℝ)..1, t * Real.log ((1 - t) / 2))) = 2 / 3

def TsgFactorStatement : Prop :=
  ∀ D k : ℕ, 1 ≤ k → 2 * k ≤ D + 1 →
    ((D + 1).choose (2 * k) : ℚ) / (D.choose (2 * k - 1) : ℚ) = ((D : ℚ) + 1) / (2 * k)

def FlatnessTestCriterion : Prop :=
  ∀ c₁ c₂ : ℚ,
    let h : ℚ → ℚ → ℚ := fun x y => 5 * x ^ 3 * y + 21 / 2 * x ^ 2 * y ^ 2 + 5 * x * y ^ 3
    let b := c₂ + c₁ / 2
    h c₁ c₂ + h (-c₁) (c₁ + c₂) = 6 * c₁ ^ 2 * b ^ 2 - c₁ ^ 4 ∧
    3 * (4 * (1 / 2) / 1) * c₁ ^ 2 * b ^ 2 - 3 / 4 * (4 * (2 / 3) / 2) * c₁ ^ 4 =
      6 * c₁ ^ 2 * b ^ 2 - c₁ ^ 4

end ReciprocityTheory.ChartRestriction.G.AI
