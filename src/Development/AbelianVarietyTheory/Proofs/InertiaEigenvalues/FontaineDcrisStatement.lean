import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FontaineDcris
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions Formalism.MainNotions.N
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ramifiedCoefficientChains_adm11 : ∀ D : D7, Formalism.MainNotions.RamifiedCoefficientChains.adm11 D := by
  first | exact @GlobalTheory.Per.DcrisExact.fontaine_dcris | exact GlobalTheory.Per.DcrisExact.fontaine_dcris | (intros; apply GlobalTheory.Per.DcrisExact.fontaine_dcris <;> assumption)
