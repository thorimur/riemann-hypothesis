import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FamilyHypothesesOfWorkingClassSevenDuties
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.EX
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.familyHypotheses_of_workingClass_sevenDuties : ∀ (𝒜 : FamClass) (eps : ℝ) (Fm : FamP eps), GlobalTheory.Fc.W3 𝒜 Fm → GlobalTheory.EX.DQ.Duty7 Fm → GlobalTheory.BigTop.FamHyp Fm := by
  first | exact @GlobalTheory.BigTop.famHyp_of_working_duty | exact GlobalTheory.BigTop.famHyp_of_working_duty | (intros; apply GlobalTheory.BigTop.famHyp_of_working_duty <;> assumption)
