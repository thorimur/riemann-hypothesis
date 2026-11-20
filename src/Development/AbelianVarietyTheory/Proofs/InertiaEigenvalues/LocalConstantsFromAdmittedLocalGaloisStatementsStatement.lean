import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalConstantsFromAdmittedLocalGaloisStatements
open Formalism Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.localConstants_from_admitted_local_Galois_statements : GlobalTheory.Published.BlochKatoLocal → Formalism.GaloisCohomology.LocalTateDualityK → Formalism.GaloisCohomology.LocalEulerCharK → ∀ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F), LiftingTheory.aux₃ D HW F 10 23 32 32 := by
  first | exact @GlobalTheory.localConstants_from_admitted_local_Galois_statements_alt | exact GlobalTheory.localConstants_from_admitted_local_Galois_statements_alt | (intros; apply GlobalTheory.localConstants_from_admitted_local_Galois_statements_alt <;> assumption)
