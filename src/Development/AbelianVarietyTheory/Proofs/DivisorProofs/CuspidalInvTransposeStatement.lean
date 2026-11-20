import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CuspidalInvTranspose
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.LocLanglands GlobalTheory.JHMult
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cuspidal_inv_transpose : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin n) k) V), IsCuspidal π → IsCuspidal (π.comp (GlobalTheory.TypeTame.invTranspose n)) := by
  first | exact @GlobalTheory.InvTransposeCusp.isCuspidal_comp_invTranspose | exact GlobalTheory.InvTransposeCusp.isCuspidal_comp_invTranspose | (intros; apply GlobalTheory.InvTransposeCusp.isCuspidal_comp_invTranspose <;> assumption)
