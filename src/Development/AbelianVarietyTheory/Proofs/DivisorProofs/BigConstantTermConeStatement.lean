import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BigConstantTermCone
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.big_constant_term_cone : GlobalTheory.ThK.KP → GlobalTheory.ThK.CTBigCone := by
  first | exact @GlobalTheory.ThK.ctBigCone | exact GlobalTheory.ThK.ctBigCone | (intros; apply GlobalTheory.ThK.ctBigCone <;> assumption)
