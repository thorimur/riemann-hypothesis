import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CapacityEquivalence
open GlobalTheory.CompanionTheory.EGlue
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.capacity_equivalence : GlobalTheory.CompanionTheory.EGlue.CapEquiv := by
  first | exact @GlobalTheory.CompanionTheory.EGlue.capEquiv | exact GlobalTheory.CompanionTheory.EGlue.capEquiv | (intros; apply GlobalTheory.CompanionTheory.EGlue.capEquiv <;> assumption)
