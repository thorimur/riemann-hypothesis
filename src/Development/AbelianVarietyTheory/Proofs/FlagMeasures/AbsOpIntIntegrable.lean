import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.CStarAlgebra.Module.Constructions
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Altitude
import Mathlib.MeasureTheory.Function.L2Space
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
import Mathlib.Topology.Sheaves.Presheaf

open MeasureTheory
open scoped InnerProductSpace

namespace GlobalTheory

theorem absOpInt_integrable {G : Type} [Group G] [TopologicalSpace G] [SecondCountableTopology G]
    [MeasurableSpace G] [BorelSpace G] (μ : Measure G) {Hp : Type} [NormedAddCommGroup Hp]
    [InnerProductSpace ℂ Hp] (π : G →* (Hp →L[ℂ] Hp)) (hn : ∀ g x, ‖π g x‖ = ‖x‖)
    (hc : ∀ x, Continuous fun g => π g x) (φ : G → ℂ) (hφ : Integrable φ μ) (y : Hp) :
    Integrable (fun g => φ g • π g y) μ := by
  refine Integrable.mono' (hφ.norm.mul_const ‖y‖) ?_ (ae_of_all _ fun g => ?_)
  · exact hφ.aestronglyMeasurable.smul (hc y).aestronglyMeasurable
  · rw [norm_smul, hn]

theorem absOpInt : ∀ (G : Type) [Group G] [TopologicalSpace G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] (μ : Measure G) (Hp : Type) [NormedAddCommGroup Hp] [InnerProductSpace ℂ Hp] [CompleteSpace Hp] (π : G →* (Hp →L[ℂ] Hp)), (∀ g x, ‖π g x‖ = ‖x‖) → (∀ x, Continuous fun g => π g x) → ∀ φ : G → ℂ, Integrable φ μ → ∃ P : Hp →L[ℂ] Hp, (∀ y, P y = ∫ g, φ g • π g y ∂μ) ∧ ∀ x y : Hp, ⟪x, P y⟫_ℂ = ∫ g, φ g * ⟪x, π g y⟫_ℂ ∂μ := by
  intro G _ _ _ _ _ μ Hp _ _ _ π hn hc φ hφ
  let L : Hp →ₗ[ℂ] Hp :=
    { toFun := fun y => ∫ g, φ g • π g y ∂μ
      map_add' := fun y z => by
        simp only [map_add, smul_add]
        exact integral_add (absOpInt_integrable μ π hn hc φ hφ y)
          (absOpInt_integrable μ π hn hc φ hφ z)
      map_smul' := fun c y => by
        simp only [map_smul, RingHom.id_apply]
        simp_rw [smul_comm (φ _) c]
        exact integral_smul c _ }
  refine ⟨L.mkContinuous (∫ g, ‖φ g‖ ∂μ) fun y => ?_, fun y => rfl, fun x y => ?_⟩
  · calc ‖L y‖ = ‖∫ g, φ g • π g y ∂μ‖ := rfl
      _ ≤ ∫ g, ‖φ g • π g y‖ ∂μ := norm_integral_le_integral_norm _
      _ = ∫ g, ‖φ g‖ * ‖y‖ ∂μ := by simp_rw [norm_smul, hn]
      _ = (∫ g, ‖φ g‖ ∂μ) * ‖y‖ := integral_mul_const _ _
  · change ⟪x, ∫ g, φ g • π g y ∂μ⟫_ℂ = _
    rw [← integral_inner (absOpInt_integrable μ π hn hc φ hφ y)]
    simp_rw [inner_smul_right]

end GlobalTheory
