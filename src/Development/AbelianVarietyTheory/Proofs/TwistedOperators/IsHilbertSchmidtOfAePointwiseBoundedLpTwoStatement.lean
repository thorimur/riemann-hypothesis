import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsHilbertSchmidtOfAePointwiseBoundedLpTwo

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta MeasureTheory Set Filter NumberField
open scoped Topology ContDiff TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isHilbertSchmidt_of_ae_pointwise_bounded_Lp_two : ∀ {X : Type} [MeasurableSpace X] {ν : Measure X} [IsFiniteMeasure ν] {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (T : H →L[ℂ] Lp ℂ 2 ν) (C : ℝ), (∀ v, ∀ᵐ x ∂ν, ‖T v x‖ ≤ C * ‖v‖) → GlobalTheory.OpTrace.IsHilbertSchmidt T := by
  first | exact @GlobalTheory.isHilbertSchmidt_of_ae_bounded | exact GlobalTheory.isHilbertSchmidt_of_ae_bounded | (intros; apply GlobalTheory.isHilbertSchmidt_of_ae_bounded <;> assumption)
