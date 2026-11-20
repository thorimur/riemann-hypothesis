import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjugateModelOfDeRham
open GlobalTheory.LatVal GlobalTheory.LatJet
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.conjugate_model_of_de_rham : GlobalTheory.Published.PeriodComparison → GlobalTheory.Published.AbelianDeRham → GlobalTheory.Published.AbelianDualCrystal → ModelConj := by
  first | exact @GlobalTheory.LatJet.modelConj_of_deRham | exact GlobalTheory.LatJet.modelConj_of_deRham | (intros; apply GlobalTheory.LatJet.modelConj_of_deRham <;> assumption)
