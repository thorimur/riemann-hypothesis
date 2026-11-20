import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.CStarAlgebra.Module.Constructions
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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

open MeasureTheory
open scoped InnerProductSpace

namespace ReciprocityTheory.ChartRestriction.DS.Mult1

def RankOneMinors : Prop :=
  ∀ (X : Type) (κ : X → X → ℂ),
    (∀ x y, κ x y = star (κ y x)) → (∀ x, 0 ≤ (κ x x).re) →
    (∀ x y x' y', κ x y * κ x' y' = κ x y' * κ x' y) →
    ∃ f : X → ℂ, ∀ x y, κ x y = f x * star (f y)

def TransposeUnitary : Prop :=
  ∀ (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
    (c : E ≃ₗᵢ⋆[ℂ] E) (w₁ : E) (y : E ≃ₗᵢ[ℂ] E),
    (∀ v, c (c v) = v) → c w₁ = w₁ →
    ∃ u₀ : E ≃ₗᵢ[ℂ] E, u₀ w₁ = w₁ ∧ ∀ v, u₀ (y (u₀.symm v)) = c (y.symm (c v))

def SchurDichotomy : Prop :=
  ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G]
    (μ : Measure G) [μ.IsMulLeftInvariant] [μ.IsInvInvariant] [μ.IsOpenPosMeasure]
    (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] [Nontrivial H]
    (θ : G → G) (ρ : G → (H →L[ℂ] H)),
    Continuous θ → (∀ a b, θ (a * b) = θ b * θ a) → (∀ g, θ (θ g) = g) → μ.map θ = μ →
    ρ 1 = 1 → (∀ a b, ρ (a * b) = (ρ a).comp (ρ b)) → (∀ g v, ‖ρ g v‖ = ‖v‖) →
    (∀ v, Continuous fun g => ρ g v) → (∀ v w, MemLp (fun g => ⟪w, ρ g v⟫_ℂ) 2 μ) →
    (∀ S : Submodule ℂ H, IsClosed (S : Set H) → (∀ g, ∀ v ∈ S, ρ g v ∈ S) → S = ⊥ ∨ S = ⊤) →
    (∀ x y x' y' : H, ∫ g, ⟪y, ρ (θ g) x⟫_ℂ * star ⟪y', ρ g x'⟫_ℂ ∂μ = 0) ∨
    ∃ C : H ≃ₗᵢ⋆[ℂ] H, (∀ g (x y : H), ⟪y, ρ (θ g) x⟫_ℂ = ⟪C x, ρ g (C y)⟫_ℂ) ∧
      ∀ h (v : H), C (ρ h v) = ρ (θ h)⁻¹ (C v)

end ReciprocityTheory.ChartRestriction.DS.Mult1
