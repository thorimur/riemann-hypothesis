import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BaseLowerBound
open GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.BigOn.Exp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.base_lower_bound : GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.GlobalArtinReciprocity → GlobalTheory.Published.RayClassFieldSt → GlobalTheory.SerStd.SeriesRatS → BaseGe := by
  first | exact @GlobalTheory.BigOn.Exp.baseGe_of | exact GlobalTheory.BigOn.Exp.baseGe_of | (intros; apply GlobalTheory.BigOn.Exp.baseGe_of <;> assumption)
