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

namespace SiegelEisensteinSeries

open Filter Topology

variable {E : Type*} [AddCommGroup E] [Module ℂ E]

def WHolo (D : Set (E →ₗ[ℂ] ℂ)) (f : ℂ → E) (U : Set ℂ) : Prop :=
  ∀ ν ∈ D, DifferentiableOn ℂ (fun s => ν (f s)) U

def Separating (D : Set (E →ₗ[ℂ] ℂ)) : Prop :=
  ∀ v : E, v ≠ 0 → ∃ ν ∈ D, ν v ≠ 0

structure LinSys (E : Type*) [AddCommGroup E] [Module ℂ E] (I : Type*) where
  a : I → ℂ → E →ₗ[ℂ] ℂ
  c : I → ℂ → ℂ

variable {I : Type*}

def LinSys.Sol (Ξ : LinSys E I) (s : ℂ) : Set E := {v | ∀ i, Ξ.a i s v = Ξ.c i s}

def LinSys.FinTypeOn (D : Set (E →ₗ[ℂ] ℂ)) (Ξ : LinSys E I) (W : Set ℂ) : Prop :=
  ∃ (k : ℕ) (Λ : ℂ → Fin k → E), (∀ j, WHolo D (fun s => Λ s j) W) ∧
    (∀ i j, DifferentiableOn ℂ (fun s => Ξ.a i s (Λ s j)) W) ∧
    ∀ s ∈ W, Ξ.Sol s ⊆ Submodule.span ℂ (Set.range (Λ s))

def LinSys.LocFinType (D : Set (E →ₗ[ℂ] ℂ)) (Ξ : LinSys E I) (Ω : Set ℂ) : Prop :=
  ∀ s₀ ∈ Ω, ∃ W : Set ℂ, IsOpen W ∧ s₀ ∈ W ∧ W ⊆ Ω ∧ Ξ.FinTypeOn D W

end SiegelEisensteinSeries
