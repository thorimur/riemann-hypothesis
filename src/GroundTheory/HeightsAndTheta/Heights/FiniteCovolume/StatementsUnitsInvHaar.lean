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

namespace GroundTheory.Heights₂.Heights.FiniteCovolume

open MeasureTheory
open scoped ENNReal NNReal

noncomputable section

instance secondCountableTopology_units_complex : SecondCountableTopology ℂˣ :=
  Units.isOpenEmbedding_val.isInducing.secondCountableTopology

instance borelSpace_units_complex : BorelSpace ℂˣ where
  measurable_eq := by
    rw [congrArg (@borel ℂˣ) Units.isOpenEmbedding_val.isInducing.eq_induced, borel_comap,
      ← BorelSpace.measurable_eq (α := ℂ)]
    rfl

def UnitsInvHaar.Statement (I : Type*) [Fintype I] : Prop :=
  ∀ (ρ : Measure (I → ℂˣ)) [ρ.IsHaarMeasure], ∃ c : ℝ≥0, c ≠ 0 ∧
    ∀ (k : ℕ) (g : (I → ℂˣ) → ℝ≥0∞) (g' : (I → ℂ) → ℝ≥0∞), Measurable g →
      (∀ (b : I → ℂ) (hb : ∀ i, b i ≠ 0), g' b = g fun i => (Units.mk0 (b i) (hb i))⁻¹) →
      ∫⁻ a, (∏ i, ‖(a i : ℂ)‖ₑ⁻¹ ^ (2 * (k + 1))) * g a ∂ρ =
        c * ∫⁻ b, (∏ i, ‖b i‖ₑ ^ (2 * k)) * g' b

end

end GroundTheory.Heights₂.Heights.FiniteCovolume
