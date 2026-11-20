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
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Topology Filter Metric

def IsCentredDiscCover {σ : Type} [Fintype σ] (Y : Set (σ → ℂ)) (w : σ → ℂ) (p : (σ → ℂ) →L[ℂ] ℂ)
    (ρ : ℝ) (N : ℕ) : Prop :=
  w ∈ Y ∧ 0 < N ∧ Set.MapsTo p Y (ball (p w) ρ) ∧ (∀ x ∈ Y, p x = p w → x = w) ∧
    (∀ t ∈ ball (p w) ρ, t ≠ p w → {x | x ∈ Y ∧ p x = t}.encard = N) ∧
    (∀ K ⊆ ball (p w) ρ, IsCompact K → IsCompact {x | x ∈ Y ∧ p x ∈ K}) ∧
    (∀ x ∈ Y, p x ≠ p w → ∃ (O : Set ℂ) (V : Set (σ → ℂ)) (g : ℂ → σ → ℂ), IsOpen O ∧ IsOpen V ∧ x ∈ V ∧
      DifferentiableOn ℂ g O ∧ (∀ t ∈ O, p (g t) = t) ∧ Y ∩ V = g '' O)

def CentredDiscCoverCurve.Statement : Prop :=
  ∀ (σ : Type) [Fintype σ] (Y : Set (σ → ℂ)) (w : σ → ℂ) (p : (σ → ℂ) →L[ℂ] ℂ) (ρ : ℝ) (N : ℕ),
    IsCentredDiscCover Y w p ρ N →
      ∃ r : ℝ, 0 < r ∧ ∃ γ : ℂ → σ → ℂ,
        DifferentiableOn ℂ γ (ball 0 r) ∧ Set.InjOn γ (ball 0 r) ∧ γ 0 = w ∧ Set.MapsTo γ (ball 0 r) Y

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
