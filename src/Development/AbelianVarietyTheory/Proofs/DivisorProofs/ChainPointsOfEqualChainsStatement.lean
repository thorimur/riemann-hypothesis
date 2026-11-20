import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChainPointsOfEqualChains
open CategoryTheory Limits AlgebraicGeometry IsLocalRing
open GlobalTheory GlobalTheory.QCoh GlobalTheory.Vert GlobalTheory.MixedLocalChains GlobalTheory.ChainPts
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.chain_points_of_equal_chains : GlobalTheory.ChainPts.EqChainSt → GlobalTheory.ChainPts.ChainPtsSt := by
  first | exact @GlobalTheory.ChainParts.chainPtsSt_of_eqChainSt | exact GlobalTheory.ChainParts.chainPtsSt_of_eqChainSt | (intros; apply GlobalTheory.ChainParts.chainPtsSt_of_eqChainSt <;> assumption)
