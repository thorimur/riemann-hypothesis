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

namespace ReciprocityTheory.ChartRestriction.G.Lift.VA

def PairSep : Prop :=
  ∀ (Ω : Type) [Field Ω] (ι : Type) [Fintype ι] (v : ι → Valuation Ω (WithZero (Multiplicative ℤ))),
    (∀ i, ∃ x, v i x = WithZero.exp (1 : ℤ)) → (∀ i j, i ≠ j → ¬ (v i).IsEquiv (v j)) →
    ∀ i j, i ≠ j → ∃ w, 1 < v i w ∧ v j w < 1

def LargeSmall : Prop :=
  ∀ (Ω : Type) [Field Ω] (ι : Type) [Fintype ι] (v : ι → Valuation Ω (WithZero (Multiplicative ℤ))),
    (∀ i, ∃ x, 1 < v i x) → (∀ i j, i ≠ j → ∃ w, 1 < v i w ∧ v j w < 1) →
    ∀ i, ∃ y, 1 < v i y ∧ ∀ j, j ≠ i → v j y < 1

def NearOne : Prop :=
  ∀ (Ω : Type) [Field Ω] (ι : Type) [Fintype ι] (v : ι → Valuation Ω (WithZero (Multiplicative ℤ))),
    (∀ i, ∃ y, 1 < v i y ∧ ∀ j, j ≠ i → v j y < 1) →
    ∀ i (ε : ι → WithZero (Multiplicative ℤ)), (∀ j, ε j ≠ 0) →
      ∃ z, v i z = 1 ∧ ∀ j, j ≠ i → v j z < ε j

def Assembly : Prop :=
  ∀ (Ω : Type) [Field Ω] (ι : Type) [Fintype ι] (v : ι → Valuation Ω (WithZero (Multiplicative ℤ))),
    (∀ i, ∃ x, v i x = WithZero.exp (1 : ℤ)) →
    (∀ i (ε : ι → WithZero (Multiplicative ℤ)), (∀ j, ε j ≠ 0) →
      ∃ z, v i z = 1 ∧ ∀ j, j ≠ i → v j z < ε j) →
    ∀ n : ι → ℤ, ∃ x : Ω, ∀ i, v i x = WithZero.exp (n i)

end ReciprocityTheory.ChartRestriction.G.Lift.VA
