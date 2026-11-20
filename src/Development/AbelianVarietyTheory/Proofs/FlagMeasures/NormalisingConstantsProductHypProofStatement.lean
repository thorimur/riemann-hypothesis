import Development.AbelianVarietyTheory.Proofs.FlagMeasures.NormalisingConstantsProductHypProof
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.normalisingConstantsProductHyp_proof : GlobalTheory.TypeAsm.ConstC := by
  first | exact @GlobalTheory.LocalConst.constC | exact GlobalTheory.LocalConst.constC | (intros; apply GlobalTheory.LocalConst.constC <;> assumption)
