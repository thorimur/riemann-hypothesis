import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PseudocoefficientSeparationOfHarishChandra
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pseudocoefficient_separation_of_harish_chandra : GlobalTheory.Published.HarishChandraAnalyticity → GlobalTheory.Published.PseudoCoefficientUpq → GlobalTheory.Published.HarishChandraCharacters → GlobalTheory.Published.LanglandsClassification → GlobalTheory.IndefiniteRowSideFullHecke.PseudoCoefficientSeparation.PseudoCoeffSeparation := by
  first | exact @GlobalTheory.SepPseudo.pseudoCoeffSeparation | exact GlobalTheory.SepPseudo.pseudoCoeffSeparation | (intros; apply GlobalTheory.SepPseudo.pseudoCoeffSeparation <;> assumption)
