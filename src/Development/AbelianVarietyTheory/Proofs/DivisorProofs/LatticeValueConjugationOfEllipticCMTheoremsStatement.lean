import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeValueConjugationOfEllipticCMTheorems
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.latticeValueConjugation_of_ellipticCM_theorems : GlobalTheory.Published.SiegelKlingenDeligneRibet → GlobalTheory.Published.PartialZetaFunctionalEquation → GlobalTheory.Published.HilbertClassFieldJ → GlobalTheory.Published.EllipticMainTheoremCM → GlobalTheory.LatVal.LatConj := by
  first | exact @GlobalTheory.LatConjEll.latConj | exact GlobalTheory.LatConjEll.latConj | (intros; apply GlobalTheory.LatConjEll.latConj <;> assumption)
