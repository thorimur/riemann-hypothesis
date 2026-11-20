import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PolarizationGlueHolds
open GlobalTheory.TorRef GlobalTheory.ShFam
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.polarization_glue_holds : PolGlueSt := by
  first | exact @GlobalTheory.TorRef.polGlueSt | exact GlobalTheory.TorRef.polGlueSt | (intros; apply GlobalTheory.TorRef.polGlueSt <;> assumption)
