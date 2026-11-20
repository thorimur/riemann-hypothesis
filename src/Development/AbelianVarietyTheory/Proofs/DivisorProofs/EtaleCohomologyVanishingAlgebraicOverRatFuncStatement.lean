import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleCohomologyVanishingAlgebraicOverRatFunc
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.etale_cohomology_vanishing_algebraic_over_ratFunc : GlobalTheory.EtC.C1 := by
  first | (exact @GlobalTheory.EtC.gaugeSplitting_holds) | (exact GlobalTheory.EtC.gaugeSplitting_holds) | (intros; apply GlobalTheory.EtC.gaugeSplitting_holds  <;> assumption)
