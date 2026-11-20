import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HilbertEisensteinExpansionOfLipschitzHeckeZeta
open GlobalTheory.LatVal GlobalTheory.LatJet
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hilbertEisensteinExpansion_of_lipschitz_hecke_zeta : GlobalTheory.IndefiniteRowSideFullHecke.TraceDualDifferent.Lipschitz → GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.HeckeWeightTwo → GlobalTheory.Published.PartialZetaFunctionalEquation → EisExp := by
  first | exact @GlobalTheory.HilbertEis.eisExp | exact GlobalTheory.HilbertEis.eisExp | (intros; apply GlobalTheory.HilbertEis.eisExp <;> assumption)
