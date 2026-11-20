import Development.AbelianVarietyTheory.Proofs.JetHarmonics.QuotientMeasureRightInvariant
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.quotientMeasure_right_invariant : PI.QuotInv := by
  first | exact @GlobalTheory.QuotRightInv.quotInv | exact GlobalTheory.QuotRightInv.quotInv | (intros; apply GlobalTheory.QuotRightInv.quotInv <;> assumption)
