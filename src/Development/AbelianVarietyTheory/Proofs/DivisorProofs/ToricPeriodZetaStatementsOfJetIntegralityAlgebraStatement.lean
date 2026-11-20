import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToricPeriodZetaOfJetIntegralityAlgebra
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.toricPeriodZetaStatements_of_jetIntegrality_algebraicity : GlobalTheory.Published.EllipticMainTheoremCM → GlobalTheory.Published.HilbertClassFieldJ → GlobalTheory.Published.SiegelKlingenDeligneRibet → GlobalTheory.Published.PartialZetaFunctionalEquation → GlobalTheory.Published.HeckeTateFunctionalEquation → GlobalTheory.LatJet.JetInt → GlobalTheory.LatVal.LatAlg → GlobalTheory.LatVal.LatConj → GlobalTheory.Mem.LiteralAutomorphy.JoinOut := by
  first | exact @GlobalTheory.JoinFun.joinOut_of_jetInt | exact GlobalTheory.JoinFun.joinOut_of_jetInt | (intros; apply GlobalTheory.JoinFun.joinOut_of_jetInt <;> assumption)
