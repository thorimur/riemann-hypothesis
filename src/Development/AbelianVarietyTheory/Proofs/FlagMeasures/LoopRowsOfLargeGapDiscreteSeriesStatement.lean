import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LoopRowsOfLargeGapDiscreteSeries
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.L2.SG.ThmSOwn
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.loopRows_of_large_gap_discreteSeries : GlobalTheory.GapIn.Hyp → Formalism.L2.SG.LocWSOf.BesselOfW → BpJoin.ThmBpDS → Formalism.L2.SG.Pf.WuDecayOfGap → Formalism.L2.SG.RowsDef.RowsFinDim → ∀ (𝒞 : FamClass) (sel : SSel 𝒞), (∀ {eps : ℝ} (Fm : FamP eps), 𝒞 Fm → TuSize Fm) → (Closed 𝒞 fun Fm _ => PX.RanksF Fm 3 (Fm.CYL + 1) (1 / 4) 3 (1 / 2) Fm.CTu) → LoopRowS 3 𝒞 sel := by
  first | exact @GlobalTheory.LoopRowsCloseGap.loop_rows_closed_gap | exact GlobalTheory.LoopRowsCloseGap.loop_rows_closed_gap | (intros; apply GlobalTheory.LoopRowsCloseGap.loop_rows_closed_gap <;> assumption)
