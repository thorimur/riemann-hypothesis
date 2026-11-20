import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalLiftingAdmittedHypothesesAll
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Module
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.localLifting_admittedHypotheses_all : GlobalTheory.Published.BlochKatoLocal → Formalism.GaloisCohomology.LocalTateDualityK → Formalism.GaloisCohomology.LocalEulerCharK → ∀ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F), ElementDenominator.Adm2 D HW F := by
  first | exact @GlobalTheory.AdmAllRecords.localLifting_admittedHypotheses_all_alt | exact GlobalTheory.AdmAllRecords.localLifting_admittedHypotheses_all_alt | (intros; apply GlobalTheory.AdmAllRecords.localLifting_admittedHypotheses_all_alt <;> assumption)
