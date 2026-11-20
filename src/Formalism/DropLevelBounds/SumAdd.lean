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

def addl (k n f : ℕ) (l1 : ℝ) (l : ℕ) : ℝ :=
  if (l : ℝ) ^ 2 < k then (f : ℝ) * (n : ℝ) ^ 3 * (k : ℝ) ^ 3 * Real.log k
  else if (l : ℝ) < l1 then (f : ℝ) * (n : ℝ) ^ 3 * l * Real.log ((n : ℝ) * l) else 0

def SumAdd : Prop :=
  ∃ C : ℝ, ∀ (k n f N : ℕ) (T m b L : ℝ), 1 ≤ k → 1 ≤ n → 1 ≤ f → 0 < T → 0 < m → 0 < b → 0 < L →
    Real.log ((n : ℝ) * (Real.sqrt (m * b / (T * f * (n : ℝ) ^ 3)) / L)) ≤ L ^ 2 →
    T * f * (n : ℝ) ^ 3 * (k : ℝ) ^ 4 ≤ m * b →
    T * (∑ l ∈ (Finset.range (N + 1)).filter Nat.Prime,
      addl k n f (Real.sqrt (m * b / (T * f * (n : ℝ) ^ 3)) / L) l * Real.log l) ≤ C * m * b

end Formalism.UnitaryBoundIntegral
