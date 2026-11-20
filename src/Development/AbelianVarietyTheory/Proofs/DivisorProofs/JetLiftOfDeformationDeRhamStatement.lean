import Development.AbelianVarietyTheory.Proofs.DivisorProofs.JetLiftOfDeformationDeRham
open GlobalTheory.LatVal GlobalTheory.LatJet
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.jet_lift_of_deformation_de_rham : GlobalTheory.Published.GrothendieckDeformation → GlobalTheory.Published.AbelianDeRham → GlobalTheory.Published.AbelianDualCrystal → JetLift := by
  first | exact @GlobalTheory.LatJet.jetLift_of_deformation_of_deRham | exact GlobalTheory.LatJet.jetLift_of_deformation_of_deRham | (intros; apply GlobalTheory.LatJet.jetLift_of_deformation_of_deRham <;> assumption)
