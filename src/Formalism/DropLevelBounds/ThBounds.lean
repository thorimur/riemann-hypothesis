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

noncomputable section
open scoped BigOperators

namespace Formalism.UnitaryBoundIntegral

def thl (k l : ℕ) : ℝ :=
  sSup {t : ℝ | ∃ i : ℕ, Odd i ∧ 3 ≤ i ∧ (k : ℝ) ^ ((3 : ℝ) / 2) < (l : ℝ) ^ i ∧ t = ((l : ℝ) ^ i)⁻¹}

def ThBounds : Prop :=
  ∀ (k l : ℕ), 1 ≤ k → 2 ≤ l →
    thl k l ≤ ((l : ℝ) ^ 3)⁻¹ ∧ thl k l < ((k : ℝ) ^ ((3 : ℝ) / 2))⁻¹ ∧
      ((k : ℝ) < (l : ℝ) ^ 2 → thl k l = ((l : ℝ) ^ 3)⁻¹)

def SumTh : Prop :=
  ∃ C : ℝ, ∀ (k N : ℕ), 1 ≤ k →
    (∑ l ∈ (Finset.range (N + 1)).filter Nat.Prime, thl k l * Real.log l) ≤ C / k

end Formalism.UnitaryBoundIntegral
