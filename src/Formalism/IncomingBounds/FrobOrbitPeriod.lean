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

namespace Formalism.IncomingBounds

def FrobOrbitSum : Prop :=
  ∀ (α : Type) [Fintype α] (φ : Equiv.Perm α) (p : ℝ), 1 < p → ∀ k : ℕ, 1 ≤ k → ∀ a : α → ℝ,
    (∑ τ : α, ((∑' n : ℕ, (p ^ ((n + 1) * k))⁻¹ * a ((φ ^ (n + 1)) τ)) - a τ / (p - 1))) =
      (1 / (p ^ k - 1) - 1 / (p - 1)) * ∑ τ : α, a τ

def FrobOrbitPeriod : Prop :=
  ∀ (α : Type) (φ : Equiv.Perm α) (p : ℝ), 1 < p → ∀ k : ℕ, 1 ≤ k → ∀ (a : α → ℝ) (τ : α)
    (f : ℕ), 1 ≤ f → (φ ^ f) τ = τ →
      (∑' n : ℕ, (p ^ ((n + 1) * k))⁻¹ * a ((φ ^ (n + 1)) τ)) =
        (∑ n ∈ Finset.range f, (p ^ ((n + 1) * k))⁻¹ * a ((φ ^ (n + 1)) τ)) /
          (1 - (p ^ (f * k))⁻¹)

end Formalism.IncomingBounds
