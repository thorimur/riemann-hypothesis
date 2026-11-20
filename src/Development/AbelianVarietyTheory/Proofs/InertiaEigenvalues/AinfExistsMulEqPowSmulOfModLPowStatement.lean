import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AinfExistsMulEqPowSmulOfModLPow
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ainf_exists_mul_eq_pow_smul_of_mod_lPow : ∀ (l : ℕ) [Fact l.Prime] (d M : ℕ) (τ : Ainf l) (Y : Matrix (Fin d) (Fin d) (Ainf l)), IsUnit (Y.map (inclW l)) → (∀ n, ∃ Q : Matrix (Fin d) (Fin d) (Ainf l), ∀ i j, (l : WCb l) ^ n ∣ (Y.map (inclW l) * Q.map (inclW l) - inclW l τ ^ M • (1 : Matrix (Fin d) (Fin d) (WCb l))) i j) → ∃ Y' : Matrix (Fin d) (Fin d) (Ainf l), Y * Y' = τ ^ M • (1 : Matrix (Fin d) (Fin d) (Ainf l)) := by
  first | exact @GlobalTheory.AinfInvLim.exists_mul_eq_smul_one | exact GlobalTheory.AinfInvLim.exists_mul_eq_smul_one | (intros; apply GlobalTheory.AinfInvLim.exists_mul_eq_smul_one <;> assumption)
