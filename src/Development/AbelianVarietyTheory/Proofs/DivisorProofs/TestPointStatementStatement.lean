import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TestPointStatement
open GlobalTheory.DetHT
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.TestPointStatement : TestPtSt := by
  first | exact @GlobalTheory.DetHT.testPtSt | exact GlobalTheory.DetHT.testPtSt | (intros; apply GlobalTheory.DetHT.testPtSt <;> assumption)
