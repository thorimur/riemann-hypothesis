import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.CStarAlgebra.Module.Constructions
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.InnerProductSpace.Adjoint
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
import Mathlib.Order.CompletePartialOrder
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
import Mathlib.Topology.Algebra.PontryaginDual
import Mathlib.Topology.Sheaves.Init

noncomputable section

open MeasureTheory ComplexConjugate ComplexOrder

namespace PI.Bochner

def PD {Γ : Type} [AddCommGroup Γ] (φ : Γ → ℂ) : Prop :=
  ∀ (N : ℕ) (g : Fin N → Γ) (c : Fin N → ℂ),
    0 ≤ ∑ i, ∑ j, c i * conj (c j) * φ (g i - g j)

def StepGNS : Prop :=
  ∀ (Γ : Type) [AddCommGroup Γ] (φ : Γ → ℂ), PD φ →
    ∃ (H : Type) (_ : NormedAddCommGroup H) (_ : InnerProductSpace ℂ H) (_ : CompleteSpace H)
      (U : Γ → H →L[ℂ] H) (ξ : H),
      U 0 = 1 ∧ (∀ a b, U (a + b) = U a * U b) ∧ (∀ a, star (U a) = U (-a)) ∧
        ∀ γ, φ γ = inner ℂ ξ (U γ ξ)

def StepAlg : Prop :=
  ∀ (Γ : Type) [AddCommGroup Γ]
    (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (U : Γ → H →L[ℂ] H) (ξ : H),
    U 0 = 1 → (∀ a b, U (a + b) = U a * U b) → (∀ a, star (U a) = U (-a)) →
    ∃ (A : Type) (_ : CommCStarAlgebra A) (u : Multiplicative Γ →* unitary A) (ω : A →ₗ[ℂ] ℂ),
      (∀ a, 0 ≤ ω (star a * a)) ∧
        ∀ γ : Γ, ω (u (Multiplicative.ofAdd γ) : A) = inner ℂ ξ (U γ ξ)

def StepRiesz : Prop :=
  ∀ (X : Type) [TopologicalSpace X] [CompactSpace X] [T2Space X] [MeasurableSpace X] [BorelSpace X]
    (Λ : C(X, ℂ) →ₗ[ℂ] ℂ), (∀ f, 0 ≤ Λ (star f * f)) →
    ∃ μ : Measure X, IsFiniteMeasure μ ∧ ∀ f : C(X, ℂ), Λ f = ∫ x, f x ∂μ

def StepGelfand : Prop :=
  ∀ (Γ : Type) [AddCommGroup Γ] (A : Type) [CommCStarAlgebra A]
    (u : Multiplicative Γ →* unitary A) (ω : A →ₗ[ℂ] ℂ), (∀ a, 0 ≤ ω (star a * a)) →
    letI : TopologicalSpace (Multiplicative Γ) := ⊥
    letI : MeasurableSpace (PontryaginDual (Multiplicative Γ)) := borel _
    ∃ μ : Measure (PontryaginDual (Multiplicative Γ)), IsFiniteMeasure μ ∧
      ∀ γ : Γ, ω (u (Multiplicative.ofAdd γ) : A)
        = ∫ χ, ((χ (Multiplicative.ofAdd γ) : Circle) : ℂ) ∂μ

end PI.Bochner
