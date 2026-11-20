import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalLiftingTheoremBHypothesesAdmitted
open Formalism Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.localLifting_theoremB_hypotheses_admitted : GlobalTheory.Published.BlochKatoLocal → Formalism.GaloisCohomology.LocalTateDualityK → Formalism.GaloisCohomology.LocalEulerCharK → ∀ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F), ArcLiftingSetup.admitted D HW F Cm 10 23 32 32 8 := by
  first | exact @GlobalTheory.TheoremBAdm.admissible_ranks_of_CMDatum | exact GlobalTheory.TheoremBAdm.admissible_ranks_of_CMDatum | (intros; apply GlobalTheory.TheoremBAdm.admissible_ranks_of_CMDatum <;> assumption)
