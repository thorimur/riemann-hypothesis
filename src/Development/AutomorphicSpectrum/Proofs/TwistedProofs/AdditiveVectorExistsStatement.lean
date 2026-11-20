import Development.AutomorphicSpectrum.Proofs.TwistedProofs.AdditiveVectorExists
open GlobalTheory.InertZeta
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.additive_vector_exists : AddVec := by
  first | exact @GlobalTheory.CompanionTheory.InertZeta.addVec | exact GlobalTheory.CompanionTheory.InertZeta.addVec | (intros; apply GlobalTheory.CompanionTheory.InertZeta.addVec <;> assumption)
