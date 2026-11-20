import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PartialZetaDenominatorsCMFieldOfSiegelKlingenDel
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.partialZetaDenominatorsCMField_of_siegelKlingenDeligneRibet : GlobalTheory.Published.SiegelKlingenDeligneRibet → GlobalTheory.IndefiniteRowSideFullHecke.ZetaValueIdeals.ZetaDenominators := by
  first | exact @GlobalTheory.ZetaDenom.zetaDenominators | exact GlobalTheory.ZetaDenom.zetaDenominators | (intros; apply GlobalTheory.ZetaDenom.zetaDenominators <;> assumption)
