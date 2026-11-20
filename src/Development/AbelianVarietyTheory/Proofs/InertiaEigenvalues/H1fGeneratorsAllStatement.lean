import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.H1fGeneratorsAll
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions Formalism.MainNotions.N
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ramifiedCoefficientChains_adm13 : ∀ D : D7, Formalism.MainNotions.RamifiedCoefficientChains.adm13 D := by
  first | exact @GlobalTheory.h1f_generators_of_record | exact GlobalTheory.h1f_generators_of_record | (intros; apply GlobalTheory.h1f_generators_of_record <;> assumption)
