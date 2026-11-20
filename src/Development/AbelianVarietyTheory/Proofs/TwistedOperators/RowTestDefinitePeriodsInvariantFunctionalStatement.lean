import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RowTestDefinitePeriodsInvariantFunctional
open GlobalTheory.RowClaim GlobalTheory.RowReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rowTest_definitePeriods_invariant_functional : Big fun ch => InvLine ch := by
  first | exact @GlobalTheory.RowReal.invLine_big | exact GlobalTheory.RowReal.invLine_big | (intros; apply GlobalTheory.RowReal.invLine_big <;> assumption)
