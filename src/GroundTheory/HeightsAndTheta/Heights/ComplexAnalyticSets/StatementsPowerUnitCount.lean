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

open Filter Topology Matrix

noncomputable section

def PowerUnitCount.Statement : Prop :=
  ∀ (d m : ℕ) (O : Set (Fin (d + 1) → ℂ)) (F : (Fin (d + 1) → ℂ) → Fin d → ℂ)
    (H : (Fin (d + 1) → ℂ) → ℂ) (s : Fin (d + 1) → ℂ),
    IsOpen O → s ∈ O → s 0 = 0 → DifferentiableOn ℂ F O → DifferentiableOn ℂ H O → H s ≠ 0 →
    Function.Bijective (fderiv ℂ (fun τ => vecCons (τ 0) (F τ)) s) →
    ∃ P₀ ∈ 𝓝 s, Set.InjOn F (P₀ ∩ {τ | τ 0 = 0}) ∧
      ∀ P ∈ 𝓝 s, P ⊆ P₀ → ∃ (V : Set (Fin d → ℂ)) (ρ : ℝ), IsOpen V ∧ F s ∈ V ∧ 0 < ρ ∧
        (∀ w ∈ V, ∀ τ ∈ P₀, τ 0 = 0 → F τ = w → τ ∈ P) ∧
        ∀ w ∈ V, ∀ t : ℂ, 0 < ‖t‖ → ‖t‖ < ρ →
          {τ | τ ∈ P ∧ F τ = w ∧ τ 0 ^ m * H τ = t}.encard = m

end

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
