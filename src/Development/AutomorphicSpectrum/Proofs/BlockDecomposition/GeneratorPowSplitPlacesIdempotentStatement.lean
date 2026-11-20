import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GeneratorPowSplitPlacesIdempotent
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.generator_pow_split_places_idempotent : PositivityTheory.Rg.BcB.F.MLM.SplitPowersOfIdempotents := by
  first | exact @GlobalTheory.CompanionTheory.SplitPlacePowers.generator_pow_split_places_of_idempotent | exact GlobalTheory.CompanionTheory.SplitPlacePowers.generator_pow_split_places_of_idempotent | (intros; apply GlobalTheory.CompanionTheory.SplitPlacePowers.generator_pow_split_places_of_idempotent <;> assumption)
