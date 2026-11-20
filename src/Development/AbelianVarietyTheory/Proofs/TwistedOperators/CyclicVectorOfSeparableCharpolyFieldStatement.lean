import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CyclicVectorOfSeparableCharpolyField
open GlobalTheory.RegSS
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cyclicVector_of_separable_charpoly_field : GlobalTheory.RegSS.CyclicField := by
  first | exact @GlobalTheory.RegSS.cyclicField | exact GlobalTheory.RegSS.cyclicField | (intros; apply GlobalTheory.RegSS.cyclicField <;> assumption)
