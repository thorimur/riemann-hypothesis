import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EquivariantChainPointsHyp
open CategoryTheory Limits AlgebraicGeometry IsLocalRing
open GlobalTheory GlobalTheory.QCoh GlobalTheory.Vert GlobalTheory.MixedLocalChains GlobalTheory.ChainPts
theorem _root_.GlobalTheory.T.equivariant_chain_points_hyp : GlobalTheory.CovTop.Hypotheses2 → GlobalTheory.CovHt.HypothesesH → GlobalTheory.Published.PrismaticDieudonnePerfd → GlobalTheory.GroupBplus.GroupAllSt → GlobalTheory.ChainPts.EqChainSt := by
  first | exact @GlobalTheory.ChainPts.eqChainSt_of_groupAllSt | exact GlobalTheory.ChainPts.eqChainSt_of_groupAllSt | (intros; apply GlobalTheory.ChainPts.eqChainSt_of_groupAllSt <;> assumption)
