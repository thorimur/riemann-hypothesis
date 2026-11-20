import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PolynomialArcHolds
open GlobalTheory.TorRef
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.polynomial_arc_holds : PolArcSt := by
  first | exact @GlobalTheory.PolArc.polArc | exact GlobalTheory.PolArc.polArc | (intros; apply GlobalTheory.PolArc.polArc <;> assumption)
