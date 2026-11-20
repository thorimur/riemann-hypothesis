import Development.AbelianVarietyTheory.Proofs.TwistedOperators.EtaleTensorQuadraticSplitAlgClosed
open GlobalTheory.RegSS
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.etale_tensor_quadratic_split_algClosed : GlobalTheory.RegSS.SplitClosed := by
  first | exact @GlobalTheory.RegSS.splitClosed | exact GlobalTheory.RegSS.splitClosed | (intros; apply GlobalTheory.RegSS.splitClosed <;> assumption)
