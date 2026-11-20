import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsFontaineThetaOnAinf
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_fontaineTheta_on_Ainf : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), ∃ θ : Ainf l →+* OC l, IsTheta AI θ := by
  first | exact @GlobalTheory.Cyc.exists_isTheta | exact GlobalTheory.Cyc.exists_isTheta | (intros; apply GlobalTheory.Cyc.exists_isTheta <;> assumption)
