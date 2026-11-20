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
import Mathlib.NumberTheory.LocalField.Basic
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

open ValuativeRel MeasureTheory

namespace PI

def GaussIntegral : Prop :=
  ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    [CharZero F] [MeasurableSpace F] [BorelSpace F] (μ : Measure F), μ.IsAddHaarMeasure →
    μ (𝒪[F] : Set F) = 1 →
  ∀ (ψ : AddChar F ℂ), Continuous ψ → (∀ x : F, (∀ y ∈ 𝒪[F], ψ (x * y) = 1) ↔ x ∈ 𝒪[F]) →
  ∀ (d : ℕ) (H : Matrix (Fin d) (Fin d) F), H.IsSymm → H.det ≠ 0 →
  ∀ (L : AddSubgroup (Fin d → F)), IsCompact (L : Set (Fin d → F)) → IsOpen (L : Set (Fin d → F)) →
  ∃ δ : ℝ, 0 < δ ∧ ∀ t : F, t ≠ 0 → (μ ((fun y => t * y) '' (𝒪[F] : Set F))).toReal < δ →
    ‖∫ x in (L : Set (Fin d → F)), ψ (dotProduct x (H.mulVec x) / (2 * t))
        ∂(Measure.pi fun _ : Fin d => μ)‖ =
      (μ ((fun y => (t⁻¹ • H).det * y) '' (𝒪[F] : Set F))).toReal ^ (-(1 / 2 : ℝ))

end PI
