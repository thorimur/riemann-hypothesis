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

open Topology Filter

def IsAnalyticNear {σ : Type} [Fintype σ] (X : Set (σ → ℂ)) (w : σ → ℂ) : Prop :=
  ∃ (N : Set (σ → ℂ)) (k : ℕ) (f : Fin k → (σ → ℂ) → ℂ), IsOpen N ∧ w ∈ N ∧
    (∀ i, AnalyticOnNhd ℂ (f i) N) ∧ X ∩ N = {z | z ∈ N ∧ ∀ i, f i z = 0}

def GermIrreducibleAt {σ : Type} [Fintype σ] (X : Set (σ → ℂ)) (w : σ → ℂ) : Prop :=
  w ∈ X ∧ ∀ f g : (σ → ℂ) → ℂ, AnalyticAt ℂ f w → AnalyticAt ℂ g w →
    (∀ᶠ z in 𝓝 w, z ∈ X → f z * g z = 0) →
      (∀ᶠ z in 𝓝 w, z ∈ X → f z = 0) ∨ (∀ᶠ z in 𝓝 w, z ∈ X → g z = 0)

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
