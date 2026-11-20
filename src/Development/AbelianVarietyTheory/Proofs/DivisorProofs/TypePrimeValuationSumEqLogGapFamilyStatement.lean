import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TypePrimeValuationSumEqLogGapFamily
open Formalism.BasicNotions Formalism.BasicNotions.DV Formalism.MainNotions NumberField Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.normDecompositionCond_famP : ∀ {eps : ℝ} (Fm : FamP eps) (x : ℝ) (hx : Fm.x1 < x) (i : Fm.Ix x), Formalism.MainNotions.WeightDegreeSizes.NormDecompositionCond (Fm.D x i) (Fm.ex x hx i).errX := by
  first | exact @GlobalTheory.TypeValNN.typePrime_valuationSum_eq_logGap_family | exact GlobalTheory.TypeValNN.typePrime_valuationSum_eq_logGap_family | (intros; apply GlobalTheory.TypeValNN.typePrime_valuationSum_eq_logGap_family <;> assumption)
