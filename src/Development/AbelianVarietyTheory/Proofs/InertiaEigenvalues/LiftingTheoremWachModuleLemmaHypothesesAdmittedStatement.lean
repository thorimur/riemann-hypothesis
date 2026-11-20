import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LiftingTheoremWachModuleLemmaHypothesesAdmitted
open Formalism Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.liftingTheorem_wachModuleLemma_hypotheses_admitted : ∀ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F), LiftingTheory.admitted D HW F Cm ∧ CrystallineLiftingBounds.admitted D HW F Cm := by
  first | exact @GlobalTheory.LiftAdmitted.all_admitted | exact GlobalTheory.LiftAdmitted.all_admitted | (intros; apply GlobalTheory.LiftAdmitted.all_admitted <;> assumption)
