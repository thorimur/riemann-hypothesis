import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MultiplicityOneAlt
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.multOne' : GlobalTheory.RealLift.MultOne := by
  first | exact @GlobalTheory.SteepMult.multOne | exact GlobalTheory.SteepMult.multOne | (intros; apply GlobalTheory.SteepMult.multOne <;> assumption)
