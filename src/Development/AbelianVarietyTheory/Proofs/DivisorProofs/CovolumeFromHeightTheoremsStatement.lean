import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CovolumeFromHeightTheorems
open GlobalTheory.CovTop GlobalTheory.BigTop
theorem _root_.GlobalTheory.T.covolume_from_height_theorems : HypothesesXH → GlobalTheory.Published.ScholzeWeinsteinB → Hypotheses3 → GlobalTheory.CovHt.HypothesesH → GlobalTheory.CovHt.Known₂ → CovolX := by
  first | exact @GlobalTheory.CovTop.AllSteps.covolX_of_scholzeWeinstein | exact GlobalTheory.CovTop.AllSteps.covolX_of_scholzeWeinstein | (intros; apply GlobalTheory.CovTop.AllSteps.covolX_of_scholzeWeinstein <;> assumption)
