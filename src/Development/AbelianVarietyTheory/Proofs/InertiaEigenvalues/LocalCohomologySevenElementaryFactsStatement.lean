import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalCohomologySevenElementaryFacts

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_cohomology_seven_elementary_facts : ReciprocityTheory.ChartRestriction.T2.Elem := by
  first | exact @GlobalTheory.LocElem.elem | exact GlobalTheory.LocElem.elem | (intros; apply GlobalTheory.LocElem.elem <;> assumption)
