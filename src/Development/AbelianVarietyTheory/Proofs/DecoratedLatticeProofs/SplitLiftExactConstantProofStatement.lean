import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitLiftExactConstantProof
open Formalism.BasicNotions
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.splitLiftExactConstant_proof : ∀ D : D7, GlobalTheory.FinPl.LiftExact D := by
  first | exact @GlobalTheory.FinPl.liftExact | exact GlobalTheory.FinPl.liftExact | (intros; apply GlobalTheory.FinPl.liftExact <;> assumption)
