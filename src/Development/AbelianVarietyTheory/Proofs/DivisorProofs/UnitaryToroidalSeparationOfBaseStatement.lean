import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryToroidalSeparationOfBase
open GlobalTheory.UChart
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitaryToroidalSeparation_of_base : UStB := by
  first | exact @GlobalTheory.UPoincTop.uStB | exact GlobalTheory.UPoincTop.uStB | (intros; apply GlobalTheory.UPoincTop.uStB <;> assumption)
