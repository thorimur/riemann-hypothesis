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

namespace Formalism.CG

def CECondition : Prop :=
  ∀ (C CE f m N t η : ℝ), 0 ≤ C → 0 ≤ f → 0 ≤ m → 0 ≤ N → 0 ≤ t → t ≤ N → 0 ≤ η → 2 * C ≤ CE →
    C * f * m * N * (N + t) + C * f * m ^ 3 * η ≤ m * CE * f * (N ^ 2 + m ^ 2 * η)

def ColumnPlaceCE : Prop :=
  ∀ (J : Finset ℕ) (col vc C CE f m N t η : ℝ) (nn : ℕ → ℝ),
    0 ≤ C → 0 ≤ f → 0 ≤ m → 0 ≤ N → 0 ≤ t → t ≤ N → 0 ≤ η → 2 * C ≤ CE → vc = 0 →
    -(∑ j ∈ J, nn j) + vc - (C * f * m * N * (N + t) + C * f * m ^ 3 * η) ≤ col →
      -(∑ j ∈ J, nn j) - m * CE * f * (N ^ 2 + m ^ 2 * η) ≤ col

end Formalism.CG
