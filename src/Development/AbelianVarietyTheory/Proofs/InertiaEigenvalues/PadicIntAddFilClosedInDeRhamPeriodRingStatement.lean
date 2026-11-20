import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PadicIntAddFilClosedInDeRhamPeriodRing
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc GlobalTheory.ExpImage
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.padicInt_add_fil_closed_in_deRhamPeriodRing : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI → ∀ (M : ℕ), 1 ≤ M → ∀ v : P.R.BdR, (∀ n : ℕ, ∃ z : ℤ_[l], qB P (z : ℚ_[l]) - v ∈ Lat AI M n) → NearZ P M v := by
  first | exact @GlobalTheory.ExpImage.nearZ_of_forall_Lat | exact GlobalTheory.ExpImage.nearZ_of_forall_Lat | (intros; apply GlobalTheory.ExpImage.nearZ_of_forall_Lat <;> assumption)
