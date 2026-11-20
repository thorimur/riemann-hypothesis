import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CentralCharacterExists
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.central_character_exists : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (x : IrrGL k) (t : kˣ), ∃ c : ℂ, Zl.ScalarBy x t c := by
  first | exact @GlobalTheory.CompanionTheory.ScalarEx.exists_scalarBy | exact GlobalTheory.CompanionTheory.ScalarEx.exists_scalarBy | (intros; apply GlobalTheory.CompanionTheory.ScalarEx.exists_scalarBy <;> assumption)
