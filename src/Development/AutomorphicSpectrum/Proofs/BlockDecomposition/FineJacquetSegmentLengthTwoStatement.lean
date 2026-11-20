import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FineJacquetSegmentLengthTwo
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.Seg
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fine_jacquet_segment_length_two : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) (hZ : GlobalTheory.Published.SegmentRepresentation) (Δ : Segment k) (h : Δ.len = 2), FineJac Δ := by
  first | exact @GlobalTheory.CompanionTheory.SegFine2.fineJac_of_len_eq_two | exact GlobalTheory.CompanionTheory.SegFine2.fineJac_of_len_eq_two | (intros; apply GlobalTheory.CompanionTheory.SegFine2.fineJac_of_len_eq_two <;> assumption)
