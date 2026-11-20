import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LocalMatchingOfHoweDuality
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_matching_of_howe_duality : GlobalTheory.Published.HoweDualityReal → GlobalTheory.FunPr.Hypotheses₂ → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.LocalMatching → GlobalTheory.SquareSt.LocalMatching := by
  first | exact @GlobalTheory.SquareLM.localMatching | exact GlobalTheory.SquareLM.localMatching | (intros; apply GlobalTheory.SquareLM.localMatching <;> assumption)
