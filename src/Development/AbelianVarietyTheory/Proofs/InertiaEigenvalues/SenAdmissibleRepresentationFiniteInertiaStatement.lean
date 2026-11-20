import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SenAdmissibleRepresentationFiniteInertia
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pst GlobalTheory.PMon TensorProduct
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sen_admissible_representation_finite_inertia : SenFinite := by
  first | exact @GlobalTheory.PMon.senFinite | exact GlobalTheory.PMon.senFinite | (intros; apply GlobalTheory.PMon.senFinite <;> assumption)
