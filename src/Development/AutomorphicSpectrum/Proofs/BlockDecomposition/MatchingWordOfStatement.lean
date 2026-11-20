import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MatchingWordOf
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.matching_word_of : PositivityTheory.Rg.BcB.F.MLM.MatchLMWordOf := by
  first | exact @GlobalTheory.CompanionTheory.MatchWord.matchLMWordOf | exact GlobalTheory.CompanionTheory.MatchWord.matchLMWordOf | (intros; apply GlobalTheory.CompanionTheory.MatchWord.matchLMWordOf <;> assumption)
