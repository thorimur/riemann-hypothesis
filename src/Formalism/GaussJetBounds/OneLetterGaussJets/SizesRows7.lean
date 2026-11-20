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

namespace Formalism.DworkPowerSeriesWeights.OddLevelGainBounds

def SizesSign7 : Prop :=
  ∀ (H : Type) [Fintype H] (c wt wt' : H → ℝ) (k : ℝ), 1 ≤ k → (∀ t, (k - 1) * wt t ≤ c t) →
    (-((k - 1) / 2) * ∑ t, min (wt t) (wt' t)) + (1 / 2) * ∑ t, c t =
        (1 / 2) * ∑ t, (c t - (k - 1) * min (wt t) (wt' t)) ∧
      0 ≤ (-((k - 1) / 2) * ∑ t, min (wt t) (wt' t)) + (1 / 2) * ∑ t, c t

def SizesRows7 : Prop :=
  ∀ (k : ℕ) (N w w' : ℝ), 1 ≤ k → 1 ≤ N →
    (∀ (row : Fin k → ℝ) (rest : ℝ), 4 * k * N ≤ w → (∀ i, w - N - 1 / 2 < row i) → 0 ≤ rest →
      ((k : ℝ) - 1) * w < (∑ i, row i) + rest) ∧
    (∀ (row : Fin (k - 1) → ℝ) (rest first : ℝ), 4 * k * N ≤ w' → (∀ i, w - N < row i) → 0 ≤ rest →
      w' - N - 1 / 2 < first → ((k : ℝ) - 1) * w < (∑ i, row i) + rest + first)

end Formalism.DworkPowerSeriesWeights.OddLevelGainBounds
