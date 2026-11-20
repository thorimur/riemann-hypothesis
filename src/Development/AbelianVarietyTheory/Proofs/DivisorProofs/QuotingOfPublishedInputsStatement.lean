import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KnownOfPublishedInputs
open GlobalTheory.CovTop GlobalTheory.CovHt
theorem _root_.GlobalTheory.T.known_of_published_inputs : GlobalTheory.CovTop.HypothesesXH → HypothesesY → Hypotheses2 → HypothesesH → GlobalTheory.Published.ScholzeWeinsteinB → GlobalTheory.Published.PoincareDeRhamDuality → GlobalTheory.LieHt.SecJets4 → (∃ r, GlobalTheory.CovTest.Ch2Const r) → Known₂ := by
  first | exact @GlobalTheory.CovHt.KnownOf.known | exact GlobalTheory.CovHt.KnownOf.known | (intros; apply GlobalTheory.CovHt.KnownOf.known <;> assumption)
