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

namespace ReciprocityTheory.ChartRestriction.G.FreeQuotientRank

def pairR {f : ℕ} (χ β : Fin f → ℝ) : ℝ := ∑ i, χ i * β i

def BetaStatement : Prop :=
  ∀ (f : ℕ) (b : Module.Basis (Fin f) ℝ (Fin f → ℝ)) (m : ℕ), 0 < m →
    let SS : Submodule ℤ (Fin f → ℝ) := Submodule.span ℤ (Set.range b)
    ∀ χ₀ ∈ SS, (∀ i, 0 ≤ χ₀ i) →
      ∃ β : Fin f → ℝ, (∀ i, 0 < β i) ∧ (∀ χ ∈ SS, ∃ z : ℤ, pairR χ β = m * z) ∧
        ∀ χ ∈ SS, (∀ i, 0 ≤ χ i) → pairR χ β = pairR χ₀ β → χ = χ₀

end ReciprocityTheory.ChartRestriction.G.FreeQuotientRank
