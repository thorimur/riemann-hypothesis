import Development.WeilBound.CoreStatements.AutomorphicKernels.SquareIntegrableSegments.SegmentSubquotients.FineJacquetSegmentLengthTwo
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.Seg
theorem _root_.GlobalTheory.TL.fine_jacquet_segment_length_two : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) (hZ : GlobalTheory.Published.SegmentRepresentation) (Δ : Segment k) (h : Δ.len = 2), FineJac Δ := by
  first | exact @GlobalTheory.CompanionTheory.LkSegFine2.fineJac_of_len_eq_two | exact GlobalTheory.CompanionTheory.LkSegFine2.fineJac_of_len_eq_two
