import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BallExistsEtaleSteinExhaustion
open MeasureTheory Filter Topology Metric ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y GlobalTheory.OTY GlobalTheory.Published.L2Extension
open scoped ENNReal ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ball_exists_etaleStein_exhaustion : ∀ (n : ℕ) (c : V n) (r : ℝ), ∃ X : EtaleStein n (ball c r), X.z = Subtype.val := by
  first | exact @GlobalTheory.BallStein.ball_etaleStein | exact GlobalTheory.BallStein.ball_etaleStein | (intros; apply GlobalTheory.BallStein.ball_etaleStein <;> assumption)
