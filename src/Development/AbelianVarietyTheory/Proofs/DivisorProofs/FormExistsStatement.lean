import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormExists
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.FormExists : GlobalTheory.RealLift.FormEx := by
  first | exact @GlobalTheory.CharPair.formEx | exact GlobalTheory.CharPair.formEx | (intros; apply GlobalTheory.CharPair.formEx <;> assumption)
