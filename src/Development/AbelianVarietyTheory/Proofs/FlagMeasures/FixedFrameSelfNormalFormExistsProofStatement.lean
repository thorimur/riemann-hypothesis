import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FixedFrameSelfNormalFormExistsProof
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fixedFrameSelfNormalFormExists_proof : GlobalTheory.TypeAsm.IdNFC := by
  first | exact @GlobalTheory.IdNF.idNFC_holds | exact GlobalTheory.IdNF.idNFC_holds | (intros; apply GlobalTheory.IdNF.idNFC_holds <;> assumption)
