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

namespace Formalism.MainNotions.LeviCoordinates

open MeasureTheory Set
open scoped ENNReal InnerProductSpace

variable {G : Type*} [Group G]

def rrk_K (Γ : Subgroup G) (φ : G → ℂ) (x y : G) : ℂ := ∑' γ : Γ, φ (x⁻¹ * (γ : G) * y)

def rrk_Kab (Γ : Subgroup G) (φ : G → ℂ) (x y : G) : ℝ≥0∞ := ∑' γ : Γ, ‖φ (x⁻¹ * (γ : G) * y)‖ₑ

theorem rrk_aesm_tsum {α ι : Type*} [MeasurableSpace α] {μ : Measure α} [Countable ι] {f : ι → α → ℂ}
    (hf : ∀ i, AEStronglyMeasurable (f i) μ) (hs : ∀ᵐ x ∂μ, Summable fun i => f i x) :
    AEStronglyMeasurable (fun x => ∑' i, f i x) μ := by
  refine aestronglyMeasurable_of_tendsto_ae (Filter.atTop : Filter (Finset ι))
    (f := fun s x => ∑ i ∈ s, f i x) (fun s => ?_) ?_
  · exact Finset.aestronglyMeasurable_fun_sum s fun i _ => hf i
  · filter_upwards [hs] with x hx
    exact hx.hasSum

end Formalism.MainNotions.LeviCoordinates

end
