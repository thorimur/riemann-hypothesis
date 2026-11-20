import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeWeightTwoContinuationOfFunctionalEquation
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heckeWeightTwoContinuation_of_functionalEquation : GlobalTheory.Published.PartialZetaFunctionalEquation → GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.HeckeWeightTwo := by
  first | exact @GlobalTheory.HeckeTwo.heckeWeightTwo_of_fe | exact GlobalTheory.HeckeTwo.heckeWeightTwo_of_fe | (intros; apply GlobalTheory.HeckeTwo.heckeWeightTwo_of_fe <;> assumption)
