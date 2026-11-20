import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ThetaSeriesIntegralUniformPrimePower
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaSeries_integral_uniform_prime_power : GlobalTheory.IndefiniteRowSideFullHecke.TwistSeries.SerInt := by
  first | exact @GlobalTheory.serInt_outright | exact GlobalTheory.serInt_outright | (intros; apply GlobalTheory.serInt_outright <;> assumption)
