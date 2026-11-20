import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FineJacquetLengthOne
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.Seg
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fine_jacquet_length_one : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) (Δ : Segment k) (h : Δ.len = 1), FineJac Δ := by
  first | exact @GlobalTheory.CompanionTheory.SegFine.fineJac_one | exact GlobalTheory.CompanionTheory.SegFine.fineJac_one | (intros; apply GlobalTheory.CompanionTheory.SegFine.fineJac_one <;> assumption)
