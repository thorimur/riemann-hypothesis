import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchActionReadingsCompatible
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.archActionReadings_compatible : GlobalTheory.RealLift.ActsLaws := by
  first | exact @GlobalTheory.RealLift.actsLaws | exact GlobalTheory.RealLift.actsLaws | (intros; apply GlobalTheory.RealLift.actsLaws <;> assumption)
