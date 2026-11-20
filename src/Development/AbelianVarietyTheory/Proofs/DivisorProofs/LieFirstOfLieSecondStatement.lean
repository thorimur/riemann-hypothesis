import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LieFirstOfLieSecond
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lieFirst_of_lieSecond' : GlobalTheory.RealLift.LieSecond → GlobalTheory.RealLift.LieFirst := by
  first | exact @GlobalTheory.RealLift.LieFirstPf.lieFirst_of_lieSecond | exact GlobalTheory.RealLift.LieFirstPf.lieFirst_of_lieSecond | (intros; apply GlobalTheory.RealLift.LieFirstPf.lieFirst_of_lieSecond <;> assumption)
