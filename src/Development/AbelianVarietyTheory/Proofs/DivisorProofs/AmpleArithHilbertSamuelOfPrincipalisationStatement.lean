import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AmpleArithHilbertSamuelOfPrincipalisation
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ampleArithHilbertSamuel_of_principalisation : GlobalTheory.Published.Principalisation → GlobalTheory.HSNef.AmpleHS := by
  first | exact @GlobalTheory.HSNef.ampleHS_of_principalisation | exact GlobalTheory.HSNef.ampleHS_of_principalisation | (intros; apply GlobalTheory.HSNef.ampleHS_of_principalisation <;> assumption)
