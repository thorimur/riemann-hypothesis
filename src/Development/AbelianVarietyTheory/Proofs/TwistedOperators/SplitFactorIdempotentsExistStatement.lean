import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SplitFactorIdempotentsExist
open GlobalTheory.RegSS
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.split_factor_idempotents_exist : GlobalTheory.RegSS.SplitIdempotents := by
  first | exact @GlobalTheory.RegSS.splitIdempotents | exact GlobalTheory.RegSS.splitIdempotents | (intros; apply GlobalTheory.RegSS.splitIdempotents <;> assumption)
