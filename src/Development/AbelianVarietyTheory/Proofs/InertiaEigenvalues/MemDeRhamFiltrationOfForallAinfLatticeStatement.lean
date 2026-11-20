import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemDeRhamFiltrationOfForallAinfLattice
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc GlobalTheory.ExpImage
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_deRhamFiltration_of_forall_ainfLattice : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI → ∀ (M : ℕ) (b : P.R.BdR), (∀ n : ℕ, b ∈ Lat AI M n) → b ∈ FilB P (M : ℤ) := by
  first | exact @GlobalTheory.ExpImage.mem_FilB_of_forall_Lat | exact GlobalTheory.ExpImage.mem_FilB_of_forall_Lat | (intros; apply GlobalTheory.ExpImage.mem_FilB_of_forall_Lat <;> assumption)
