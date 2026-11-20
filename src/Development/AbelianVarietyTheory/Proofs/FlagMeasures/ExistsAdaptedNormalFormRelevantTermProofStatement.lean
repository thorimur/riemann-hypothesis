import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsAdaptedNormalFormRelevantTermProof
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_adaptedNormalForm_relevantTerm : GlobalTheory.TypeAsm.NFExC := by
  first | exact @GlobalTheory.TypeAsm.nfExC_holds | exact GlobalTheory.TypeAsm.nfExC_holds | (intros; apply GlobalTheory.TypeAsm.nfExC_holds <;> assumption)
