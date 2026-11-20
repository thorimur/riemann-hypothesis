import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralityResult
open GlobalTheory.HalfGeo
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integrality_result : IntSt := by
  first | exact @GlobalTheory.HalfGeo.IntProof.intSt | exact GlobalTheory.HalfGeo.IntProof.intSt | (intros; apply GlobalTheory.HalfGeo.IntProof.intSt <;> assumption)
