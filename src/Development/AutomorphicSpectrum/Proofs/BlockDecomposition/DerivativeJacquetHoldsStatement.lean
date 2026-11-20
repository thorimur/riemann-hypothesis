import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DerivativeJacquetHolds
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.derivative_jacquet_holds : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], GlobalTheory.Published.IrreducibleAdmissibleGL → GlobalTheory.BZSeg.DerivJac k := by
  first | exact @GlobalTheory.CompanionTheory.BZDerivJac.derivJac_main | exact GlobalTheory.CompanionTheory.BZDerivJac.derivJac_main | (intros; apply GlobalTheory.CompanionTheory.BZDerivJac.derivJac_main <;> assumption)
