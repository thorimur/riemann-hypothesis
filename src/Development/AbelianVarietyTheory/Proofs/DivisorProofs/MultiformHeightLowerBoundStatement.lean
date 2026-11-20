import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MultiformHeightLowerBound
open NumberField MvPolynomial ReciprocityTheory.MultiplicativeHeights ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.ChowHt GlobalTheory.Adelic GlobalTheory.HermTools GlobalTheory.HilbertSamuel GlobalTheory.HSChoice GlobalTheory.HSShort
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.multiformHeight_lowerBound : HtLow := by
  first | exact @GlobalTheory.HtLowProof.htLow | exact GlobalTheory.HtLowProof.htLow | (intros; apply GlobalTheory.HtLowProof.htLow <;> assumption)
