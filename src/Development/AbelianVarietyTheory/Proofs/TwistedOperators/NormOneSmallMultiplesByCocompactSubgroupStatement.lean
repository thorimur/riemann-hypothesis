import Development.AbelianVarietyTheory.Proofs.TwistedOperators.NormOneSmallMultiplesByCocompactSubgroup
open GlobalTheory.RegSS
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.normOne_small_multiples_by_cocompact_subgroup : GlobalTheory.RegSS.NormOnePacking := by
  first | exact @GlobalTheory.RegSS.normOnePacking | exact GlobalTheory.RegSS.normOnePacking | (intros; apply GlobalTheory.RegSS.normOnePacking <;> assumption)
