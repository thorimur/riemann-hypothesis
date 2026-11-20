import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FineJacquetSegmentInduction
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.Seg
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fine_jacquet_segment_induction : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) (Δ : Segment k) (h3 : 3 ≤ Δ.len) (ih : ∀ Δ' : Segment k, Δ'.len < Δ.len → FineJac Δ'), FineJac Δ := by
  first | exact @GlobalTheory.CompanionTheory.SegFine.fineJac_step | exact GlobalTheory.CompanionTheory.SegFine.fineJac_step | (intros; apply GlobalTheory.CompanionTheory.SegFine.fineJac_step <;> assumption)
