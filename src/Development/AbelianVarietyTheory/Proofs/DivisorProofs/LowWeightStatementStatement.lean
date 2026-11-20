import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LowWeightStatement
open GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.BigOn.Exp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.low_weight_statement : LowAt := by
  first | exact @GlobalTheory.BigOn.Exp.lowAt_holds | exact GlobalTheory.BigOn.Exp.lowAt_holds | (intros; apply GlobalTheory.BigOn.Exp.lowAt_holds <;> assumption)
