import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NormLeOfQBMemLat
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc GlobalTheory.ExpImage
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.norm_le_of_qB_mem_Lat_alt : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI → ∀ (M n : ℕ), 1 ≤ M → ∀ z : ℚ_[l], qB P z ∈ Lat AI M n → ‖z‖ ≤ (l : ℝ) ^ (-(n : ℤ)) := by
  first | exact @GlobalTheory.ExpImage.norm_le_of_qB_mem_Lat | exact GlobalTheory.ExpImage.norm_le_of_qB_mem_Lat | (intros; apply GlobalTheory.ExpImage.norm_le_of_qB_mem_Lat <;> assumption)
