import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PolynomialMapHolds
open GlobalTheory.TorRef
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.polynomial_map_holds : PolMapSt := by
  first | exact @GlobalTheory.TorRef.polMapSt | exact GlobalTheory.TorRef.polMapSt | (intros; apply GlobalTheory.TorRef.polMapSt <;> assumption)
