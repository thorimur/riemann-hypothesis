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

namespace Formalism.LogVandermondeBounds.TaylorLogMetric

open Finset

def EvenOddPowerQuotientLowerBound : Prop :=
  ∀ (p i j : ℕ), 2 ≤ p → i ≤ j → (i, j) ≠ (0, 0) →
    ((p : ℚ) - 2) + 1 / ((p : ℚ) - 1) ≤
      (((p : ℚ) ^ 2) ^ i + (p : ℚ) * ((p : ℚ) ^ 2) ^ j) / ((p : ℚ) ^ 2 - 1) - ((i : ℚ) + j + 1)

def EvenOddPowerQuotientEqualityCases : Prop :=
  ∀ (p : ℕ), 2 ≤ p →
    ((((p : ℚ) ^ 2) ^ 0 + (p : ℚ) * ((p : ℚ) ^ 2) ^ 1) / ((p : ℚ) ^ 2 - 1) - (0 + 1 + 1) =
      ((p : ℚ) - 2) + 1 / ((p : ℚ) - 1)) ∧
    ((((p : ℚ) ^ 2) ^ 1 + (p : ℚ) * ((p : ℚ) ^ 2) ^ 1) / ((p : ℚ) ^ 2 - 1) - (1 + 1 + 1) =
      ((p : ℚ) - 2) + 1 / ((p : ℚ) - 1))

def LegendreFactorialBound : Prop :=
  ∀ (p i : ℕ), p.Prime → 1 ≤ i → (p - 1) * padicValNat p i.factorial ≤ i - 1

open Classical in

noncomputable def coefL (p a : ℕ) : ℚ :=
  if h : ∃ j, a = (p ^ 2) ^ j then 1 / (p : ℚ) ^ (Classical.choose h) else 0

open Classical in
noncomputable def coefG (p a : ℕ) : ℚ :=
  if h : ∃ j, a = p * (p ^ 2) ^ j then 1 / (p : ℚ) ^ (Classical.choose h + 1) else 0

open Classical in

noncomputable def coefA (p a b : ℕ) : ℚ :=
  if h : ∃ i j, i ≤ j ∧ a = (p ^ 2) ^ i ∧ b = p * (p ^ 2) ^ j then
    1 / (p : ℚ) ^ (Classical.choose h + Classical.choose (Classical.choose_spec h) + 1) else 0

noncomputable def coefB (p a b : ℕ) : ℚ := coefA p b a

def LogarithmSeriesIdentities : Prop :=
  ∀ (p : ℕ), p.Prime →
    (∀ a : ℕ, (if p ∣ a then coefG p (a / p) else 0) = coefL p a - (if a = 1 then 1 else 0)) ∧
    (∀ a b : ℕ, (if p ∣ a ∧ p ∣ b then coefA p (a / p) (b / p) else 0) =
      (p : ℚ) * (coefG p a * coefL p b - coefB p a b))

def UnitaryDeterminantPhase : Prop :=
  ∀ (n : ℕ) (δ : Matrix (Fin n) (Fin n) ℂ), δ ∈ Matrix.unitaryGroup (Fin n) ℂ →
    (1 - δ⁻¹).det ≠ 0 →
    (starRingEnd ℂ) (1 - δ⁻¹).det / (1 - δ⁻¹).det = (-1) ^ n * δ.det

end Formalism.LogVandermondeBounds.TaylorLogMetric
