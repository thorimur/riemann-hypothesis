import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CentralCharacterNormEqPow
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.central_character_norm_eq_pow : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (x : IrrGL k), 0 < x.1 → ∃ s : ℝ, ∀ (t : kˣ) (c : ℂ), Zl.ScalarBy x t c → ‖c‖ = nabs k t ^ ((x.1 : ℝ) * s) := by
  first | exact @GlobalTheory.CompanionTheory.CentralExp.norm_scalarBy_eq_nabs_rpow | exact GlobalTheory.CompanionTheory.CentralExp.norm_scalarBy_eq_nabs_rpow | (intros; apply GlobalTheory.CompanionTheory.CentralExp.norm_scalarBy_eq_nabs_rpow <;> assumption)
