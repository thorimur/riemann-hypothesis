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

namespace Formalism.SA.P7

def PackCount : Prop :=
  ∀ (ι : Type) [Fintype ι] [Nonempty ι] (V : ι → Type) [∀ v, NormedAddCommGroup (V v)]
    [∀ v, NormedSpace ℝ (V v)] [∀ v, FiniteDimensional ℝ (V v)] (N : ℕ),
    (∀ v, Module.finrank ℝ (V v) = N) →
    ∀ (S : Finset (∀ v, V v)) (lam : ℝ) (X : ι → ℝ), 0 < lam → (∀ v, 0 < X v) →
      (∀ x ∈ S, ∀ y ∈ S, x ≠ y →
        lam ≤ (∏ v, ‖x v - y v‖) ^ ((1 : ℝ) / Fintype.card ι)) →
      (∀ x ∈ S, ∀ v, ‖x v‖ ≤ X v) →
      (S.card : ℝ) ≤
        (1 + 2 * (∏ v, X v) ^ ((1 : ℝ) / Fintype.card ι) / lam) ^ (N * Fintype.card ι)

end Formalism.SA.P7
