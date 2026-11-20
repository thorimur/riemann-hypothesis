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

namespace Formalism.YangianSpanCharacter.E

def GGRatio : Prop :=
  ∀ (g : ℝ), 1 < g → ∀ k : ℕ,
    g ^ (∑ i ∈ Finset.Ico 1 k, i) / ∏ i ∈ Finset.Ico 1 k, (g ^ i - 1) =
      ∏ i ∈ Finset.Ico 1 k, (1 - (g ^ i)⁻¹)⁻¹

def GGProd : Prop :=
  ∀ (g : ℝ), 3 ≤ g → ∀ k : ℕ, ∏ i ∈ Finset.Ico 1 k, (1 - (g ^ i)⁻¹)⁻¹ ≤ 1 + 3 / g

def GGBound : Prop :=
  ∀ (g : ℝ), 3 ≤ g → ∀ (k : ℕ) (dimπ : ℝ), ∏ i ∈ Finset.Ico 1 k, (g ^ i - 1) ≤ dimπ →
    g ^ (∑ i ∈ Finset.Ico 1 k, i) / dimπ ≤ 1 + 3 / g

def SpanChar : Prop :=
  ∀ (K V : Type) [Field K] [AddCommGroup V] [Module K V] (O : Subring K) (θ : K),
    θ ∈ O → θ ≠ 0 → ∀ (n : ℕ) (f f' : Fin n → V), LinearIndependent K (Sum.elim f f') →
    ∀ α α' : Fin n → K,
      (θ⁻¹ • (∑ i, α i • f i + ∑ i, α' i • f' i) ∈
          Submodule.span O (Set.range f ∪ Set.range (fun i => θ⁻¹ • (f' i - f i))) ↔
        ∀ i, α' i ∈ O ∧ ∃ x ∈ O, α i + α' i = θ * x)

end Formalism.YangianSpanCharacter.E
