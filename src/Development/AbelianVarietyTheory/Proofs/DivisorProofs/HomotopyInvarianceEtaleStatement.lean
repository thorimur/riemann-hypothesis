import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HomotopyInvarianceEtale
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.homotopy_invariance_etale_alt : GlobalTheory.EtC.C4 := by
  first | (exact @GlobalTheory.EtC.HomotopyInv.homotopy_invariance_etale) | (exact GlobalTheory.EtC.HomotopyInv.homotopy_invariance_etale) | (intros; apply GlobalTheory.EtC.HomotopyInv.homotopy_invariance_etale  <;> assumption)
