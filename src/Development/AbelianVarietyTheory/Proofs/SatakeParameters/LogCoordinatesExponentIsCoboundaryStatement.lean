import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LogCoordinatesExponentIsCoboundary
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.log_coordinates_exponent_is_coboundary : Formalism.L2.KerInert.BeCob.CobExact := by
  first | exact @GlobalTheory.CobExactProof.cobExact | exact GlobalTheory.CobExactProof.cobExact | (intros; apply GlobalTheory.CobExactProof.cobExact <;> assumption)
