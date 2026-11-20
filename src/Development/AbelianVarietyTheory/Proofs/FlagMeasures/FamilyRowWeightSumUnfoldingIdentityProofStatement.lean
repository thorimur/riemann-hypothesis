import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FamilyRowWeightSumUnfoldingIdentityProof
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.familyRowWeightSumUnfoldingIdentity : GlobalTheory.SnFam.FamilyWeightSumUnfoldingIdentity := by
  first | exact @GlobalTheory.SnFam.familyRowWeightSumUnfoldingIdentity_proof | exact GlobalTheory.SnFam.familyRowWeightSumUnfoldingIdentity_proof | (intros; apply GlobalTheory.SnFam.familyRowWeightSumUnfoldingIdentity_proof <;> assumption)
