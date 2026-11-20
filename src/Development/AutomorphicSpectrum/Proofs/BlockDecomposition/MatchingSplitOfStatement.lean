import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MatchingSplitOf
open GlobalTheory.BCT GlobalTheory.UnitaryBC PositivityTheory.Rg.Bc.ArchbcB.B PositivityTheory.Rg.BcB.F.MT
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.matching_split_of : MatchSplitOf := by
  first | exact @GlobalTheory.CompanionTheory.MatchPowers.matchSplitOf | exact GlobalTheory.CompanionTheory.MatchPowers.matchSplitOf | (intros; apply GlobalTheory.CompanionTheory.MatchPowers.matchSplitOf <;> assumption)
