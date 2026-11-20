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

open Filter Topology

namespace EisTube

variable {ι : Type}

def reV (z : ι → ℂ) : ι → ℝ := fun i => (z i).re

def imV (z : ι → ℂ) : ι → ℝ := fun i => (z i).im

def tube (Ω : Set (ι → ℝ)) : Set (ι → ℂ) := {z | reV z ∈ Ω}

def farCone {J : Type*} [Fintype ι] (a : J → ι → ℝ) (R : ℝ) : Set (ι → ℝ) :=
  {x | ∀ j, R < ∑ i, x i * a j i}

def TubeExtends [Fintype ι] (P : Type*) [TopologicalSpace P] [FirstCountableTopology P] : Prop :=
  ∀ (Ω : Set (ι → ℝ)), IsOpen Ω → IsPreconnected Ω →
  (∀ x : ι → ℝ, ∃ x₁ ∈ Ω, ∃ x₂ ∈ Ω, x = midpoint ℝ x₁ x₂) →
  ∀ (h : P → ℝ), (∀ p, 0 ≤ h p) → (∀ p, ∃ U ∈ 𝓝 p, BddAbove (h '' U)) →
  ∀ (F : (ι → ℂ) → P → ℂ),
  (∀ p, DifferentiableOn ℂ (fun z => F z p) (tube Ω)) →
  (∀ z ∈ tube Ω, Continuous (F z)) →
  (∀ K ⊆ Ω, IsCompact K → ∃ (C : ℝ) (N : ℕ), ∀ z : ι → ℂ, reV z ∈ K → ∀ p,
      ‖F z p‖ ≤ C * h p * (1 + ‖imV z‖) ^ N) →
  ∃ G : (ι → ℂ) → P → ℂ,
    (∀ p, Differentiable ℂ (fun z => G z p)) ∧
    (∀ z ∈ tube Ω, ∀ p, G z p = F z p) ∧
    Continuous (Function.uncurry G) ∧
    (∀ K : Set (ι → ℂ), IsCompact K → ∃ C : ℝ, ∀ z ∈ K, ∀ p, ‖G z p‖ ≤ C * h p)

end EisTube
