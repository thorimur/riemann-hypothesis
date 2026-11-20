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

open Finset

noncomputable section

namespace Formalism.IrreducibleCountingLemmas.GaloisIrreducibility

def StretchedExponentialDominance : Prop :=
  ∀ C ε : ℝ, 0 < ε → ∀ᶠ x : ℝ in Filter.atTop,
    x ^ C * Real.exp (-x ^ (ε / 6)) ≤ 1 / 20 * Real.exp (-x ^ (ε / 7))

def SubsetSumCountReformulated : Prop :=
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (deg : ι → ℕ) (i : ℕ), (∀ c, 1 ≤ deg c) →
    ((Finset.univ : Finset ι).powerset.filter (fun I => ∑ c ∈ I, deg c = i)).card
      ≤ (∑ c, deg c).choose i

def TorusCountBounds : Prop :=
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (deg : ι → ℕ) (g k : ℕ) (c : ℕ → ℝ) (n : ℝ),
    (∀ x, 1 ≤ deg x) → 1 ≤ g → 1 ≤ k →
    (∀ i, c i = (((Finset.univ : Finset ι).powerset.filter
      (fun I => ∑ x ∈ I, deg x = i)).card : ℝ)) →
    n = (∑ i ∈ Finset.range k, c i * ((g : ℝ) ^ (k - i) - (g : ℝ) ^ (k - i - 1))) + c k →
    (g : ℝ) ^ k - (g : ℝ) ^ (k - 1) ≤ n ∧
      n ≤ (g : ℝ) ^ k * (1 + 1 / (g : ℝ)) ^ (∑ x, deg x)

def TorusWeightArithmetic : Prop :=
  ∀ (d : Multiset ℕ) (g k : ℕ) (n : ℝ), (∀ x ∈ d, 1 ≤ x) → 2 ≤ g → 1 ≤ k → k + 1 ≤ d.sum →
    2 * d.sum ≤ g → (g : ℝ) ^ k - (g : ℝ) ^ (k - 1) ≤ n →
    n ≤ (g : ℝ) ^ k * (1 + 1 / (g : ℝ)) ^ d.sum →
    (1 - 1 / (g : ℝ)) / (g : ℝ) ^ d.sum ≤
        n / ((g : ℝ) ^ k * (d.map (fun x => (g : ℝ) ^ x - 1)).prod) ∧
      n / ((g : ℝ) ^ k * (d.map (fun x => (g : ℝ) ^ x - 1)).prod) ≤
        (1 + 6 * (d.sum : ℝ) / g) / (g : ℝ) ^ d.sum

end Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
