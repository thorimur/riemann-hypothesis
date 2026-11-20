import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RationalSeriesOfReciprocityHypotheses
open GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.BigOn.Exp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rational_series_of_reciprocity_hypotheses : GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.GlobalArtinReciprocity → GlobalTheory.Published.RayClassFieldSt → GlobalTheory.IndefiniteRowSideFullHecke.RationalRayLevels.SeriesRat → GlobalTheory.BigOn.Exp.SerRef := by
  first | exact @GlobalTheory.SerRefPt.serRef | exact GlobalTheory.SerRefPt.serRef | (intros; apply GlobalTheory.SerRefPt.serRef <;> assumption)
