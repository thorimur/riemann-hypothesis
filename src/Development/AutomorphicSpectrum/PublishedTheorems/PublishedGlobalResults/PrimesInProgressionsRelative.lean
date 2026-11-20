import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Altitude
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LSeries.DirichletContinuation
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

open scoped BigOperators Classical
open NumberField

noncomputable section

namespace GlobalTheory.CompanionTheory

def PrimesInProgressionsRelative : Prop :=
  ∃ C₀ C c cQ c₁ : ℝ, 0 < C₀ ∧ 0 < C ∧ 0 < c ∧ 0 < cQ ∧ 0 < c₁ ∧ ∀ (N : ℕ) [NeZero N], ∃ (β : ℝ) (θ : ZMod N → ℝ),
    (((∀ a, θ a = 0) ∧ ∀ (χ : DirichletCharacter ℂ N) (b : ℝ), 1 - c₁ / Real.log (4 * N) ≤ b → b < 1 →
        DirichletCharacter.LFunction χ b ≠ 0) ∨
      (∃ χ₁ : DirichletCharacter ℂ N, (∀ a, χ₁ a = (θ a : ℂ)) ∧ 1 / 2 ≤ β ∧ β < 1 ∧
        cQ / ((4 * N : ℝ) ^ 2 * Real.log (4 * N)) ≤ 1 - β ∧ DirichletCharacter.LFunction χ₁ β = 0 ∧
        ∀ (χ : DirichletCharacter ℂ N) (b : ℝ), 1 - c₁ / Real.log (4 * N) ≤ b → b < 1 →
          DirichletCharacter.LFunction χ b = 0 → χ = χ₁ ∧ b = β)) ∧
    ∀ a : ZMod N, IsUnit a → ∀ X : ℝ, (4 * N : ℝ) ^ C₀ ≤ X →
      |(((Finset.Icc 1 ⌊X⌋₊).filter (fun p : ℕ => p.Prime ∧ (p : ZMod N) = a)).card : ℝ) -
          ((∫ t in (2 : ℝ)..X, 1 / Real.log t) - θ a * ∫ t in (2 : ℝ)..X ^ β, 1 / Real.log t) / (Nat.totient N : ℝ)| ≤
        (C * Real.exp (-(c * Real.log X / Real.log (4 * N))) + C * Real.exp (-(c * Real.sqrt (Real.log X)))) *
          (((∫ t in (2 : ℝ)..X, 1 / Real.log t) - θ a * ∫ t in (2 : ℝ)..X ^ β, 1 / Real.log t) / (Nat.totient N : ℝ))

end GlobalTheory.CompanionTheory
