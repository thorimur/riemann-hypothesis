import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CanonicalProjection
open GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.BigOn.Exp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.canonical_projection : CanProj := by
  first | exact @GlobalTheory.BigOn.Exp.canProj | exact GlobalTheory.BigOn.Exp.canProj | (intros; apply GlobalTheory.BigOn.Exp.canProj <;> assumption)
