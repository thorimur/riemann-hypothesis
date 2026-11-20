import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GramMatrixResult
open GlobalTheory.HalfGeo
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.gram_matrix_result : GramSt := by
  first | exact @GlobalTheory.HalfGeo.gram | exact GlobalTheory.HalfGeo.gram | (intros; apply GlobalTheory.HalfGeo.gram <;> assumption)
