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
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.FlagBundles

open MeasureTheory

noncomputable section

def IntervalMomentsDetermine.Statement : Prop :=
  ∀ μ ν : Measure ℝ, IsFiniteMeasure μ → IsFiniteMeasure ν →
    μ (Set.Icc (-1 : ℝ) 1)ᶜ = 0 → ν (Set.Icc (-1 : ℝ) 1)ᶜ = 0 →
    (∀ k : ℕ, ∫ x, x ^ k ∂μ = ∫ x, x ^ k ∂ν) → μ = ν

example : IsFiniteMeasure (Measure.dirac (0 : ℝ)) ∧ Measure.dirac (0 : ℝ) (Set.Icc (-1 : ℝ) 1)ᶜ = 0 ∧
    IsFiniteMeasure ((2⁻¹ : ENNReal) • (volume : Measure ℝ).restrict (Set.Icc (-1) 1)) ∧
    ((2⁻¹ : ENNReal) • (volume : Measure ℝ).restrict (Set.Icc (-1) 1)) (Set.Icc (-1 : ℝ) 1)ᶜ = 0 := by
  refine ⟨inferInstance, ?_, ?_, ?_⟩
  · rw [Measure.dirac_apply' _ (measurableSet_Icc.compl)]
    simp
  · exact ⟨by simp [ENNReal.mul_lt_top]⟩
  · simp [Measure.restrict_apply measurableSet_Icc.compl]

end

end GroundTheory.Heights₂.Heights.FlagBundles
