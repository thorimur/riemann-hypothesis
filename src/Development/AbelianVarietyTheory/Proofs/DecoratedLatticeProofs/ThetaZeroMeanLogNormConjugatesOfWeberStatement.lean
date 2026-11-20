import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaZeroMeanLogNormConjugatesOfWeber
open NumberField Formalism.BasicNotions Formalism.MainNotions.TaylorLogMetric GlobalTheory.Glob.IntegralWittCoefficients GlobalTheory.IndefiniteRowSideFullHecke
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaZero_mean_log_norm_conjugates_of_weber : PeriodLatticeAgreement.LatticePeriodEta → ThetaConstantWeber.ThetaWeberStatement → SignedLogMeans.Theta0Mean := by
  first | exact @GlobalTheory.Theta0MeanCore.theta0Mean | exact GlobalTheory.Theta0MeanCore.theta0Mean | (intros; apply GlobalTheory.Theta0MeanCore.theta0Mean <;> assumption)
