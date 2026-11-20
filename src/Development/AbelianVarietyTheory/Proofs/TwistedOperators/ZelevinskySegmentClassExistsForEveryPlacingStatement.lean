import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ZelevinskySegmentClassExistsForEveryPlacing
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.JHMult
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.zelevinskySegmentClass_exists_for_every_placing : GlobalTheory.Published.SegmentRepresentation → ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], ∃ Z : ∀ Δ : Segment k, IrrCl (GL (Fin (Δ.len * Δ.d)) k), IsSegmentClass k Z := by
  first | exact @GlobalTheory.segmentClass_exists | exact GlobalTheory.segmentClass_exists | (intros; apply GlobalTheory.segmentClass_exists <;> assumption)
