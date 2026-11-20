import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DetRestrictRangeIdempotentMatrix
open GlobalTheory.RegSS
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.det_restrict_range_idempotent_matrix : GlobalTheory.RegSS.IdempotentDet := by
  first | exact @GlobalTheory.RegSS.idempotentDet | exact GlobalTheory.RegSS.idempotentDet | (intros; apply GlobalTheory.RegSS.idempotentDet <;> assumption)
