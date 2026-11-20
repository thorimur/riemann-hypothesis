import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AcrisLpowDvdBoundTeichmullerMonoid
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.acris_lpow_dvd_bound_teichmullerMonoid : ∀ (l : ℕ) [Fact l.Prime] (y : Ainf l), WittVector.constantCoeff y ≠ 0 → ∃ C : ℕ, ∀ (z : ℤ_[l]) (N : ℕ), z ≠ 0 → (l : Per.Acris l) ^ N ∣ ainfToAcris l y * algebraMap ℤ_[l] (Per.Acris l) z → N ≤ z.valuation + C := by
  first | exact @GlobalTheory.AcrisMonBound.main | exact GlobalTheory.AcrisMonBound.main | (intros; apply GlobalTheory.AcrisMonBound.main <;> assumption)
