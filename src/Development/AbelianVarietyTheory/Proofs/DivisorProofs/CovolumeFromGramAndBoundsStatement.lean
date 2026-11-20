import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CovolumeFromGramAndBounds
open GlobalTheory.CovTop GlobalTheory.BigTop
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.covolume_from_gram_and_bounds : Gram → Rec → Cut → Bad → abelian₂ → Size → CoreLe → Low → CovolX := by
  first | exact @GlobalTheory.CovTop.Assembly.covolX_of_steps | exact GlobalTheory.CovTop.Assembly.covolX_of_steps | (intros; apply GlobalTheory.CovTop.Assembly.covolX_of_steps <;> assumption)
