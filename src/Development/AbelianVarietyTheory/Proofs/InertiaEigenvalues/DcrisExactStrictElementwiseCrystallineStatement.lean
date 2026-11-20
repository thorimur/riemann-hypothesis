import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DcrisExactStrictElementwiseCrystalline
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions Formalism.MainNotions.N
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dcris_exact_strict_elementwise_crystalline : ∀ D : D7, Formalism.MainNotions.TruncatedSeriesCountingBounds.adm9 D := by
  first | exact @GlobalTheory.dcris_exact_strict_elementwise | exact GlobalTheory.dcris_exact_strict_elementwise | (intros; apply GlobalTheory.dcris_exact_strict_elementwise <;> assumption)
