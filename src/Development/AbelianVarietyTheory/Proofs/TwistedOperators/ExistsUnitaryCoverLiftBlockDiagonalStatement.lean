import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsUnitaryCoverLiftBlockDiagonal
open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.PolarU Matrix MeasureTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_unitaryCover_lift_blockDiagonal : ∀ (p q : ℕ) (T : GrpData p q), ∀ U ∈ Matrix.unitaryGroup (Fin p) ℂ, ∀ V ∈ Matrix.unitaryGroup (Fin q) ℂ, ∃ k ∈ T.Kset, matG T k = Matrix.fromBlocks U 0 0 V := by
  first | exact @GlobalTheory.PolarU.exists_lift_blocks | exact GlobalTheory.PolarU.exists_lift_blocks | (intros; apply GlobalTheory.PolarU.exists_lift_blocks <;> assumption)
