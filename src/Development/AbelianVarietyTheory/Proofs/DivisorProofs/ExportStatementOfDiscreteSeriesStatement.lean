import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExportStatementOfDiscreteSeries
open GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.BigOn.Exp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.export_statement_of_discrete_series : GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.GlobalArtinReciprocity → GlobalTheory.Published.RayClassFieldSt → GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.CasselmanWallach → GlobalTheory.SerStd.SeriesRatS → ExportSt := by
  first | exact @GlobalTheory.BigOn.Exp.exportSt_of_hypotheses | exact GlobalTheory.BigOn.Exp.exportSt_of_hypotheses | (intros; apply GlobalTheory.BigOn.Exp.exportSt_of_hypotheses <;> assumption)
