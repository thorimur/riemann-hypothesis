import Development.AbelianVarietyTheory.Proofs.JetHarmonics.WignerMapsThreePlacesExists
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.wignerMapsThreePlaces_exists : GlobalTheory.WigSh.AmapsShExists := by
  first | exact @GlobalTheory.WigSh.amapsShExists | exact GlobalTheory.WigSh.amapsShExists | (intros; apply GlobalTheory.WigSh.amapsShExists <;> assumption)
