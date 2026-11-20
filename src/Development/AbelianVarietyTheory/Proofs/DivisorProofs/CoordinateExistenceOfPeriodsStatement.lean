import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoordinateExistenceOfPeriods
open GlobalTheory.LatVal GlobalTheory.LatJet GlobalTheory.LatJet.An
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.coordinate_existence_of_periods : GlobalTheory.Published.GaussManinPeriods → JetCalc → DiagFrame → CoordEx := by
  first | exact @GlobalTheory.LatJet.An.coordEx | exact GlobalTheory.LatJet.An.coordEx | (intros; apply GlobalTheory.LatJet.An.coordEx <;> assumption)
