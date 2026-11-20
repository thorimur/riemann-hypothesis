import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.InducedInPrincipalSeries
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.Published GlobalTheory.SplitWeil
open GroundTheory.Automorphic.Spherical

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.induced_in_principal_series : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (α : Fin n → ℂˣ) (f : IndSp (points (Fin n)) ((GlobalTheory.SmGL.ofChar (torusChar fun i => unrChar k (α i))).comp (leviTorus k (Fin n)).symm.toMonoidHom)), (fun g => f.1.1 g) ∈ principalSeriesSpace k n (paramChar k α) := by
  first | exact @GlobalTheory.CompanionTheory.SphSupp.PsBridge.indSp_mem_principalSeriesSpace | exact GlobalTheory.CompanionTheory.SphSupp.PsBridge.indSp_mem_principalSeriesSpace | (intros; apply GlobalTheory.CompanionTheory.SphSupp.PsBridge.indSp_mem_principalSeriesSpace <;> assumption)
