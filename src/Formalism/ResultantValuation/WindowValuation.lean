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
import Mathlib.NumberTheory.Padics.PadicIntegers
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

namespace Formalism.ResultantValuation

def LTEUnit : Prop :=
  ∀ (l : ℕ) [Fact l.Prime], l ≠ 2 → ∀ u : ℤ_[l], (u - 1).valuation = 1 →
    ∀ i : ℕ, 1 ≤ i → ((u ^ i - 1).valuation : ℕ) = 1 + padicValNat l i

def WindowValuation : Prop :=
  ∀ l b S : ℕ, l.Prime → 1 ≤ b →
    ((∑ i ∈ Finset.Ico b (b + S), padicValNat l i : ℕ) : ℝ) ≤
      (S : ℝ) / ((l : ℝ) - 1) + (Nat.log l (b + S) : ℝ)

def WindowKappaEq : Prop :=
  ∀ (l : ℕ) [Fact l.Prime], l ≠ 2 → ∀ u : ℤ_[l], (u - 1).valuation = 1 →
    ∀ b S : ℕ, 1 ≤ b →
      (∏ i ∈ Finset.Ico b (b + S), (1 - u ^ i)).valuation =
        S + ∑ i ∈ Finset.Ico b (b + S), padicValNat l i

def WindowKappa : Prop :=
  ∀ (l : ℕ) [Fact l.Prime], l ≠ 2 → ∀ u : ℤ_[l], (u - 1).valuation = 1 →
    ∀ b S : ℕ, 1 ≤ b →
      ((∏ i ∈ Finset.Ico b (b + S), (1 - u ^ i)).valuation : ℝ) ≤
        (S : ℝ) + (S : ℝ) / ((l : ℝ) - 1) + (Nat.log l (b + S) : ℝ)

end Formalism.ResultantValuation
