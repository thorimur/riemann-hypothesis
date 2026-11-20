import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumLambdaPullRhoIdentity
open Matrix MeasureTheory Set Filter Topology
open GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe GlobalTheory.TorsionForm GlobalTheory.TorsionForm.OneVec
open scoped Real ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sum_lambda_pull_rho_identity : ∀ {n g : ℕ} (a : Fin n → ℂ) (w : Ext (1 + 1 + g)), ∑ S : Finset (Fin (1 + 1)), lamL S (pullFullL a (rhoL (n := n) S w)) = w := by
  first | exact @GlobalTheory.TorsionForm.OneVec.Reassemble.sum_lam_pull_rho | exact GlobalTheory.TorsionForm.OneVec.Reassemble.sum_lam_pull_rho | (intros; apply GlobalTheory.TorsionForm.OneVec.Reassemble.sum_lam_pull_rho <;> assumption)
