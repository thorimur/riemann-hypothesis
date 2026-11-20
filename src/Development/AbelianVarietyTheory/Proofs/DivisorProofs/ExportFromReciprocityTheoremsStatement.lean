import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExportFromReciprocityTheorems
open GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.BigOn.Exp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.export_from_reciprocity_theorems : GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.GlobalArtinReciprocity → GlobalTheory.Published.RayClassFieldSt → GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.CasselmanWallach → GlobalTheory.SerStd.SeriesRatS → ExportSt := by
  first | exact @GlobalTheory.BigOn.exportSt_of_reading | exact GlobalTheory.BigOn.exportSt_of_reading | (intros; apply GlobalTheory.BigOn.exportSt_of_reading <;> assumption)
