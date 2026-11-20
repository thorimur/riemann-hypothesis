import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinBetaUniqueModEPow
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.breuilKisin_beta_unique_mod_E_pow : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (m N d : ℕ) (ρ : ↥(GK K) → Matrix (Fin d) (Fin d) (ℤ_[l])) (F : Frame bk N d ρ) (k k' : ℕ) (β β' : Matrix (Fin d) (Fin d) (bk.S)), F.IsBeta m k β → F.IsBeta m k' β' → ∀ i j, bk.E ^ m ∣ ((l : bk.S) ^ k' • β - (l : bk.S) ^ k • β') i j := by
  first | exact @GlobalTheory.BKLim.beta_unique | exact GlobalTheory.BKLim.beta_unique | (intros; apply GlobalTheory.BKLim.beta_unique <;> assumption)
