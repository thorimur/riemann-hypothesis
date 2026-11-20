import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.TraceEPowerHighestWeightValueGeneratingSeries
open MvPolynomial Formalism.GradedWeylDivisibility Formalism.BasicNotions GlobalTheory.Alc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.traceEPowerHighestWeightValue_generating_series : ∀ (R : Type) [CommRing R] (N : ℕ) (μ : Fin N → R), (1 - PowerSeries.X * PowerSeries.mk (hcVal R μ)) * ∏ i, (1 - PowerSeries.C (shift R μ i) * PowerSeries.X) = ∏ i, (1 - PowerSeries.C (shift R μ i + 1) * PowerSeries.X) := by
  first | exact @GlobalTheory.Alc.hcVal_generating | exact GlobalTheory.Alc.hcVal_generating | (intros; apply GlobalTheory.Alc.hcVal_generating <;> assumption)
