import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DeRhamFiltrationDuality
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.de_rham_filtration_duality : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI → ∀ K : FinExt l, drDualCore (P.PD K) ∧ Formalism.MainNotions.LocalSituation.filDualCore (P.PD K) := by
  first | exact @GlobalTheory.TateDualTied.main | exact GlobalTheory.TateDualTied.main | (intros; apply GlobalTheory.TateDualTied.main <;> assumption)
