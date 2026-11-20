import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Interval.Basic
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

namespace GroundTheory.Heights₂.Heights.FiniteCovolume

open MeasureTheory
open scoped ENNReal NNReal

noncomputable section

def SemidirectHaar.Statement (G T : Type*) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [LocallyCompactSpace G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
    [Group T] [TopologicalSpace T] [IsTopologicalGroup T] [LocallyCompactSpace T]
    [SecondCountableTopology T] [MeasurableSpace T] [BorelSpace T] : Prop :=
  ∀ (P H : Subgroup G), IsClosed (P : Set G) → IsClosed (H : Set G) → H ≤ P →
    ∀ (τ : T →* G) (β : P → T) (δ : T → ℝ≥0), Continuous τ → Continuous β → Continuous δ →
    (∀ t, τ t ∈ P) → (∀ t, ∀ x ∈ H, τ t * x * (τ t)⁻¹ ∈ H) → (∀ t, τ t ∈ H → t = 1) →
    (∀ p : P, (p : G) * (τ (β p))⁻¹ ∈ H) →
    ∀ (μ : Measure P) [μ.IsHaarMeasure] (ν : Measure H) [ν.IsHaarMeasure]
      (ρ : Measure T) [ρ.IsHaarMeasure],
    (∀ (t : T) (f : G → ℝ≥0∞), Measurable f →
      ∫⁻ x, f (τ t * x * (τ t)⁻¹) ∂ν = δ t * ∫⁻ x, f x ∂ν) →
    ∃ c : ℝ≥0, c ≠ 0 ∧ ∀ φ : G → ℝ≥0∞, Measurable φ →
      ∫⁻ p, φ p ∂μ = c * ∫⁻ t, δ t * ∫⁻ x : H, φ (x * τ t) ∂ν ∂ρ

section Inhabitants

open GaussianPlane

end Inhabitants

end

end GroundTheory.Heights₂.Heights.FiniteCovolume
