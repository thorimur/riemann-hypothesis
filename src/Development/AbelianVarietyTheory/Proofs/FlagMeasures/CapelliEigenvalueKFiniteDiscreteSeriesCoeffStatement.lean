import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CapelliEigenvalueKFiniteDiscreteSeriesCoeff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.capelli_eigenvalue_kFinite_discreteSeries_coeff : PI.KFinSmooth → PI.DSInfCharCap.DSInfCharCap → PI.CapelliEig.CapEig := by
  first | exact @GlobalTheory.CapelliEigenvalue.capEig | exact GlobalTheory.CapelliEigenvalue.capEig | (intros; apply GlobalTheory.CapelliEigenvalue.capEig <;> assumption)
