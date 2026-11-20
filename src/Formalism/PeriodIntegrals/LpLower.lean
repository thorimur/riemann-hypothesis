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

namespace PI

def lpFeasible (l d : ℕ) [NeZero d] (Ds : ZMod d → ℝ) : Set ℝ :=
  {y | ∃ xs : ZMod d → ℕ → ℝ, (∀ s i, 0 ≤ xs s i) ∧
    (∀ s i, (¬ Odd i ∨ d ≤ i) → xs s i = 0) ∧
    (∀ s, (∑ i ∈ Finset.range d, (l : ℝ) ^ i * xs s i) +
      (∑ i ∈ Finset.range d, xs (s - (i : ZMod d)) i) ≤ Ds s) ∧
    y = ∑ s, ∑ i ∈ Finset.range d, xs s i}

def lpF (l d : ℕ) [NeZero d] (Ds : ZMod d → ℝ) : ℝ :=
  (l : ℝ) / ((l : ℝ) ^ 2 - 1) * (∑ s, Ds s) - sSup (lpFeasible l d Ds)

def LpLower : Prop :=
  ∀ (l d : ℕ) [NeZero d] (Ds : ZMod d → ℝ), 2 ≤ l → (∀ s, 0 ≤ Ds s) →
    (∑ s, Ds s) / ((l : ℝ) ^ 2 - 1) ≤ lpF l d Ds

end PI
