import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.JacquetSubLeftOfAdmissible
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.jacquet_sub_left_of_admissible : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], GlobalTheory.Published.IrreducibleAdmissibleGL → JacquetSubLeft k := by
  first | exact @GlobalTheory.CompanionTheory.JacquetLeft.jacquetSubLeft | exact GlobalTheory.CompanionTheory.JacquetLeft.jacquetSubLeft | (intros; apply GlobalTheory.CompanionTheory.JacquetLeft.jacquetSubLeft <;> assumption)
