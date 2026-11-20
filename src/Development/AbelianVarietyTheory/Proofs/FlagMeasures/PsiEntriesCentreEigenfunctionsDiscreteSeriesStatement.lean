import Development.AbelianVarietyTheory.Proofs.FlagMeasures.PsiEntriesCentreEigenfunctionsDiscreteSeries
open GlobalTheory.Dec
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.psiEntries_centreEigenfunctions_discreteSeries : PsiEigen := by
  first | exact @GlobalTheory.Dec.PsiEig.psiEigen | exact GlobalTheory.Dec.PsiEig.psiEigen | (intros; apply GlobalTheory.Dec.PsiEig.psiEigen <;> assumption)
