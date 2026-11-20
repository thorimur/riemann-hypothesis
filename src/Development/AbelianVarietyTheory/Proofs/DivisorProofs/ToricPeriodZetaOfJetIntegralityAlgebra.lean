import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToricPeriodZetaOfLatticeValueStatementsStatement

theorem GlobalTheory.JoinFun.joinOut_of_jetInt : GlobalTheory.Published.EllipticMainTheoremCM → GlobalTheory.Published.HilbertClassFieldJ → GlobalTheory.Published.SiegelKlingenDeligneRibet → GlobalTheory.Published.PartialZetaFunctionalEquation → GlobalTheory.Published.HeckeTateFunctionalEquation → GlobalTheory.LatJet.JetInt → GlobalTheory.LatVal.LatAlg → GlobalTheory.LatVal.LatConj → GlobalTheory.Mem.LiteralAutomorphy.JoinOut := by
  intro hEM hHCF hSKDR hPZ hHT hJetInt hLatAlg hLatConj
  have hS44 := GlobalTheory.T.cmLattice_derivClassInvariance_of_hecke (GlobalTheory.T.heckeWeightTwoContinuation_of_functionalEquation hPZ)
  exact GlobalTheory.T.toricPeriodZeta_of_latticeValue_statements hEM hHCF hSKDR hHT (GlobalTheory.T.latticeValueIntegrality_ramified_of_expansion hS44 (GlobalTheory.JetExp.expansion_of_jetInt hJetInt))
    (GlobalTheory.T.latticeValueIntegrality_unramified_of_jetIntegrality hS44 hJetInt) hLatAlg hLatConj
