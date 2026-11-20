import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TestResultOfPoint
open GlobalTheory.HalfGeo
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.test_result_of_point : PtSt → TestSt := by
  first | exact @GlobalTheory.HalfGeo.testSt_of_ptSt | exact GlobalTheory.HalfGeo.testSt_of_ptSt | (intros; apply GlobalTheory.HalfGeo.testSt_of_ptSt <;> assumption)
