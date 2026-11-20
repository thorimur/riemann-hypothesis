import Development.AbelianVarietyTheory.Proofs.DivisorProofs.JetDeterminantOfDeRham
open GlobalTheory.LatVal GlobalTheory.LatJet GlobalTheory.LatJet.An
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.jet_determinant_of_de_rham : GlobalTheory.Published.AbelianDeRham → JetCalc → JetDet := by
  first | exact @GlobalTheory.LatJet.An.Det.jetDet | exact GlobalTheory.LatJet.An.Det.jetDet | (intros; apply GlobalTheory.LatJet.An.Det.jetDet <;> assumption)
