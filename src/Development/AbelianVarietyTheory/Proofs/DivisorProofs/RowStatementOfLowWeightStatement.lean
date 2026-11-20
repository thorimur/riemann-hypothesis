import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RowStatementOfLowWeight
open GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.BigOn.Exp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.row_statement_of_low_weight : GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.GlobalArtinReciprocity → GlobalTheory.Published.RayClassFieldSt → GlobalTheory.SerStd.SeriesRatS → LowAt → TwAdm → RowAt := by
  first | exact @GlobalTheory.BigOn.Exp.rowAt_of | exact GlobalTheory.BigOn.Exp.rowAt_of | (intros; apply GlobalTheory.BigOn.Exp.rowAt_of <;> assumption)
