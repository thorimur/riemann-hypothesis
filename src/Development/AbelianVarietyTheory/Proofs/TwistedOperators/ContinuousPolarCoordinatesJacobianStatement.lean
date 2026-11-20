import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ContinuousPolarCoordinatesJacobian
open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.PolarU Matrix MeasureTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.continuous_polarCoordinatesJacobian : ∀ (p q : ℕ), Continuous (polJ : Mat p q → ℝ) := by
  first | exact @GlobalTheory.PolarU.continuous_polJ | exact GlobalTheory.PolarU.continuous_polJ | (intros; apply GlobalTheory.PolarU.continuous_polJ <;> assumption)
