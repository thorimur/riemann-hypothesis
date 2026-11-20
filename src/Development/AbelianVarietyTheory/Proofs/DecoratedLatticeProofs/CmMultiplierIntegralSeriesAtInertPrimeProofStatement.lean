import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CmMultiplierIntegralSeriesAtInertPrimeProof
open PowerSeries GlobalTheory.Honda Formalism.L2.Th1.CM
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cmMultiplierIntegralSeriesAtInertPrime_proof : EndOmega := by
  first | exact @GlobalTheory.Honda.endOmega_holds | exact GlobalTheory.Honda.endOmega_holds | (intros; apply GlobalTheory.Honda.endOmega_holds <;> assumption)
