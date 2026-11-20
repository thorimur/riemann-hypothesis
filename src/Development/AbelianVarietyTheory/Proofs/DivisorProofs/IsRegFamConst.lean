import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.CStarAlgebra.Classes
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

namespace GlobalTheory.CuspDbl

open Metric

def IsRegFam {Y : Type} [TopologicalSpace Y] (ht : Y → ℝ) (s₀ : ℂ) (Ez : ℂ → Y → Y → ℂ) : Prop :=
  ∀ s₁ : ℂ, ∃ (k : ℕ) (r C : ℝ) (N : ℕ) (Hf : ℂ → Y → Y → ℂ), 0 < r ∧ (s₁ = s₀ → k = 0) ∧
    (∀ s ∈ ball s₁ r, (s ≠ s₁ ∨ k = 0) → ∀ h h', Hf s h h' = (s - s₁) ^ k * Ez s h h') ∧
    (∀ h h', DifferentiableOn ℂ (Hf · h h') (ball s₁ r)) ∧
    (∀ s ∈ ball s₁ r, Continuous fun x : Y × Y => Hf s x.1 x.2) ∧
    ∀ s ∈ ball s₁ r, ∀ h h', ‖Hf s h h'‖ ≤ C * (ht h * ht h') ^ N

end GlobalTheory.CuspDbl

end
