import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SmoothContinuousConvolutionRealPointsUnitary
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec
open scoped InnerProductSpace ComplexOrder ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.smooth_continuous_convolution_realPointsUnitary : ∀ (I : AutInst) (a F : I.Ginf → ℂ), SmoothInf I a → HasCompactSupport a → LocallyIntegrable F (muInf I) → SmoothInf I (fun y => ∫ g, F g * a (y⁻¹ * g) ∂(muInf I)) ∧ Continuous (fun y => ∫ g, F g * a (y⁻¹ * g) ∂(muInf I)) := by
  first | exact @GlobalTheory.SmoothConv.smooth_convolution | exact GlobalTheory.SmoothConv.smooth_convolution | (intros; apply GlobalTheory.SmoothConv.smooth_convolution <;> assumption)
