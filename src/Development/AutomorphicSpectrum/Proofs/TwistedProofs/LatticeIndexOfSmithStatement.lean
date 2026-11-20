import Development.AutomorphicSpectrum.Proofs.TwistedProofs.LatticeIndexOfSmith
open GlobalTheory.InertZeta
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lattice_index_of_smith : Smith → LatIndex := by
  first | exact @GlobalTheory.CompanionTheory.InertIndex.latIndex | exact GlobalTheory.CompanionTheory.InertIndex.latIndex | (intros; apply GlobalTheory.CompanionTheory.InertIndex.latIndex <;> assumption)
