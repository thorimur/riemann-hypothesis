import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CovolumeOfHeightHyp
open GlobalTheory.CovTop GlobalTheory.BigTop
theorem _root_.GlobalTheory.T.covolume_of_height : Slim → HypothesesXH → (∃ r, GlobalTheory.CovTest.Ch2Const r) → CovolX := by
  first | exact @GlobalTheory.CovTop.covolX_of_slim | exact GlobalTheory.CovTop.covolX_of_slim | (intros; apply GlobalTheory.CovTop.covolX_of_slim <;> assumption)
