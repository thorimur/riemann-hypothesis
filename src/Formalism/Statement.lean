import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Altitude
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Harmonic.EulerMascheroni
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

open Complex MeasureTheory Set Filter Topology

noncomputable section

namespace Formalism

open ArithmeticFunction in

def LamF {N : ℕ} (χ : DirichletCharacter ℂ N) (n : ℕ) : ℝ :=
  Λ n * (1 + (χ n).re)

def S {N : ℕ} (χ : DirichletCharacter ℂ N) (x : ℝ) : ℝ :=
  ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, LamF χ n * (x / n - 1)

def gammaF {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) : ℝ :=
  Real.eulerMascheroniConstant +
    (deriv (DirichletCharacter.LFunction χ) 1 / DirichletCharacter.LFunction χ 1).re

def G {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (x : ℝ) : ℝ :=
  S χ x - x * Real.log x + (1 + gammaF χ) * x

instance fact_prime_seven : Fact (Nat.Prime 7) := ⟨by norm_num⟩

def quadraticCharFour : DirichletCharacter ℂ 4 := ZMod.χ₄.ringHomComp (Int.castRingHom ℂ)

def quadraticCharThree : DirichletCharacter ℂ 3 := (quadraticChar (ZMod 3)).ringHomComp (Int.castRingHom ℂ)

def quadraticCharacterMod7 : DirichletCharacter ℂ 7 := (quadraticChar (ZMod 7)).ringHomComp (Int.castRingHom ℂ)

def LandauStep : Prop :=
  ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N), χ ≠ 1 → (∀ n : ℕ, (χ n).im = 0) →
  ∀ σ₀ : ℝ, 0 < σ₀ → σ₀ < 1 →
  (∀ σ : ℝ, σ₀ < σ → σ < 1 → DirichletCharacter.LFunction χ σ ≠ 0) →
  (∃ C : ℝ, ∀ x : ℝ, 1 ≤ x → -C * x ^ σ₀ ≤ G χ x) →
  ∀ s : ℂ, σ₀ < s.re → riemannZeta s ≠ 0 ∧ DirichletCharacter.LFunction χ s ≠ 0

def LandauStepEps : Prop :=
  ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N), χ ≠ 1 → (∀ n : ℕ, (χ n).im = 0) →
  ∀ σ₀ : ℝ, 0 ≤ σ₀ → σ₀ < 1 →
  (∀ σ : ℝ, σ₀ < σ → σ < 1 → DirichletCharacter.LFunction χ σ ≠ 0) →
  (∀ ε : ℝ, 0 < ε → ∃ C : ℝ, ∀ x : ℝ, 1 ≤ x → -C * x ^ (σ₀ + ε) ≤ G χ x) →
  ∀ s : ℂ, σ₀ < s.re → riemannZeta s ≠ 0 ∧ DirichletCharacter.LFunction χ s ≠ 0

def RHofG {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) : Prop :=
  (∀ ε : ℝ, 0 < ε → ∃ C : ℝ, ∀ x : ℝ, 1 ≤ x → -C * x ^ ((1 : ℝ) / 2 + ε) ≤ G χ x) →
  RiemannHypothesis ∧ ∀ s : ℂ, 1 / 2 < s.re → DirichletCharacter.LFunction χ s ≠ 0

end Formalism
