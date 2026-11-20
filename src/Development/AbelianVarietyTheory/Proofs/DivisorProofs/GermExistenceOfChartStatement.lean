import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GermExistenceOfChart
open GlobalTheory.LatVal GlobalTheory.LatJet GlobalTheory.LatJet.An
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.germ_existence_of_chart : Chart → HolLift → GermEx := by
  first | exact @GlobalTheory.LatJet.An.germEx_of_chart_holLift | exact GlobalTheory.LatJet.An.germEx_of_chart_holLift | (intros; apply GlobalTheory.LatJet.An.germEx_of_chart_holLift <;> assumption)
