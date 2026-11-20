import Development.AbelianVarietyTheory.Proofs.FlagMeasures.PsiEntriesRealAnalytic
open GlobalTheory.Dec
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.psi_entries_real_analytic : PsiAnalytic := by
  first | exact @GlobalTheory.Dec.psiAnalytic | exact GlobalTheory.Dec.psiAnalytic | (intros; apply GlobalTheory.Dec.psiAnalytic <;> assumption)
