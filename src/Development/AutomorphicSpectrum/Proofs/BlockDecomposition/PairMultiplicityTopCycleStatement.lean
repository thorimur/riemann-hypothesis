import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PairMultiplicityTopCycle
open GlobalTheory.CompanionTheory.PairMult
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pair_multiplicity_top_cycle : GlobalTheory.CompanionTheory.PairMult.TopCyc := by
  first | exact @GlobalTheory.CompanionTheory.PairMult.TopCycQ.topCyc | exact GlobalTheory.CompanionTheory.PairMult.TopCycQ.topCyc | (intros; apply GlobalTheory.CompanionTheory.PairMult.TopCycQ.topCyc <;> assumption)
