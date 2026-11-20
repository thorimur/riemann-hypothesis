import Development.AbelianVarietyTheory.Proofs.DivisorProofs.JetCalculusStatement
open GlobalTheory.LatVal GlobalTheory.LatJet GlobalTheory.LatJet.An
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.jet_calculus_statement : JetCalc := by
  first | exact @GlobalTheory.JetCalcPf.jetCalc | exact GlobalTheory.JetCalcPf.jetCalc | (intros; apply GlobalTheory.JetCalcPf.jetCalc <;> assumption)
