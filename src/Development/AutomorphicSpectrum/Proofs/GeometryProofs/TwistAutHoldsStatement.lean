import Development.AutomorphicSpectrum.Proofs.GeometryProofs.TwistAutHolds
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.TwistAut_holds : GlobalTheory.CompanionTheory.Ar.TwistAut := by
  first | exact @GlobalTheory.CompanionTheory.Ar.TwistAutProof.twistAut | exact GlobalTheory.CompanionTheory.Ar.TwistAutProof.twistAut | (intros; apply GlobalTheory.CompanionTheory.Ar.TwistAutProof.twistAut <;> assumption)
