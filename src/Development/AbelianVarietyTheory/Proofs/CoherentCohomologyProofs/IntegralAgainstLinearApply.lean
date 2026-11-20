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
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Monotonicity.Lemmas
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

open MeasureTheory

namespace GlobalTheory.IntegralAgainstMeasure

variable {K B : Type*} [TopologicalSpace K] [CompactSpace K] [MeasurableSpace K]
  [OpensMeasurableSpace K] [NormedAddCommGroup B] [NormedSpace ℂ B]

theorem integrable_smul (μ : Measure K) [IsFiniteMeasure μ] (p : C(K, B)) (f : C(K, ℂ)) :
    Integrable (fun k => f k • p k) μ :=
  (f.continuous.smul p.continuous).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

noncomputable def integralAgainstLinear (μ : Measure K) [IsFiniteMeasure μ] (p : C(K, B)) :
    C(K, ℂ) →ₗ[ℂ] B where
  toFun f := ∫ k, f k • p k ∂μ
  map_add' f g := by
    simp only [ContinuousMap.add_apply, add_smul]
    exact integral_add (integrable_smul μ p f) (integrable_smul μ p g)
  map_smul' c f := by
    simp only [ContinuousMap.smul_apply, smul_assoc, RingHom.id_apply]
    exact integral_smul c _

@[simp] theorem integralAgainstLinear_apply (μ : Measure K) [IsFiniteMeasure μ] (p : C(K, B))
    (f : C(K, ℂ)) : integralAgainstLinear μ p f = ∫ k, f k • p k ∂μ := rfl

theorem norm_integral_smul_le (μ : Measure K) [IsFiniteMeasure μ] (p : C(K, B)) (f : C(K, ℂ)) :
    ‖∫ k, f k • p k ∂μ‖ ≤ (μ.real Set.univ * ‖p‖) * ‖f‖ := by
  have h : ∀ᵐ k ∂μ, ‖f k • p k‖ ≤ ‖p‖ * ‖f‖ := Filter.Eventually.of_forall fun k => by
    rw [norm_smul, mul_comm]
    exact mul_le_mul (p.norm_coe_le_norm k) (f.norm_coe_le_norm k) (norm_nonneg _) (norm_nonneg _)
  calc ‖∫ k, f k • p k ∂μ‖ ≤ ‖p‖ * ‖f‖ * μ.real Set.univ := norm_integral_le_of_norm_le_const h
    _ = (μ.real Set.univ * ‖p‖) * ‖f‖ := by ring

noncomputable def integralAgainst (μ : Measure K) [IsFiniteMeasure μ] (p : C(K, B)) :
    C(K, ℂ) →L[ℂ] B :=
  (integralAgainstLinear μ p).mkContinuous (μ.real Set.univ * ‖p‖) (norm_integral_smul_le μ p)

@[simp] theorem integralAgainst_apply (μ : Measure K) [IsFiniteMeasure μ] (p : C(K, B))
    (f : C(K, ℂ)) : integralAgainst μ p f = ∫ k, f k • p k ∂μ := rfl

end GlobalTheory.IntegralAgainstMeasure
