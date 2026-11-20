import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PairingBoundInfinitePlaces
open Matrix PositivityTheory.Rg.BcB.D1
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pairing_bound_infinite_places : DetMono → PairI := by
  first | exact @GlobalTheory.CompanionTheory.Wedge.pairI_of_detMono | exact GlobalTheory.CompanionTheory.Wedge.pairI_of_detMono | (intros; apply GlobalTheory.CompanionTheory.Wedge.pairI_of_detMono <;> assumption)
