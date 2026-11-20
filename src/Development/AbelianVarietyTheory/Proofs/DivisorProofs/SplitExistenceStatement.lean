import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SplitExistence
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.split_existence : GlobalTheory.ThK.KP → GlobalTheory.ThK.SplitEx := by
  first | exact @GlobalTheory.ThKSplit.splitEx | exact GlobalTheory.ThKSplit.splitEx | (intros; apply GlobalTheory.ThKSplit.splitEx <;> assumption)
