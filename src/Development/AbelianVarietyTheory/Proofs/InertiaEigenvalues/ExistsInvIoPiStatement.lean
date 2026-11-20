import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsInvIoPi
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc GlobalTheory.ExpImage
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_inv_io_pi_alt : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI → ∃ u ∈ FilB P 0, io AI AI.π₁ * u = 1 := by
  first | exact @GlobalTheory.ExpImage.exists_inv_io_pi | exact GlobalTheory.ExpImage.exists_inv_io_pi | (intros; apply GlobalTheory.ExpImage.exists_inv_io_pi <;> assumption)
