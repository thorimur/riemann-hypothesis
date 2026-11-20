import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WeilRepresentationContinuity
open GlobalTheory.CompanionTheory.ThTot
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weil_representation_continuity : WeilCont := by
  first | exact @GlobalTheory.CompanionTheory.ThTot.weilCont | exact GlobalTheory.CompanionTheory.ThTot.weilCont | (intros; apply GlobalTheory.CompanionTheory.ThTot.weilCont <;> assumption)
