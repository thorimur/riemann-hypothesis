import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CMLatticeDividedPowerJetIntegralityOfHyp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cmLatticeDividedPowerJetIntegrality_of_ellipticCM : GlobalTheory.Published.SiegelKlingenDeligneRibet → GlobalTheory.Published.PartialZetaFunctionalEquation → GlobalTheory.Published.HilbertClassFieldJ → GlobalTheory.Published.EllipticMainTheoremCM → GlobalTheory.LatJet.JetInt := by
  first | exact @GlobalTheory.JetIntElliptic.jetInt | exact GlobalTheory.JetIntElliptic.jetInt | (intros; apply GlobalTheory.JetIntElliptic.jetInt <;> assumption)
