import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.TowerTheoremBAveraged
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology GlobalTheory.CompanionTheory.Ar.Top
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tower_theorem_B_averaged : ∀ II : IntersectionSystem, ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N : ℕ) (T : RootTower Ψ N) (hh : RP Ψ N →ₗ[ℝ] ℝ), T.ThmB II hh → T.PropA II → LabelInv (Ψ := Ψ) (N := N) hh → T.ThmBA II hh := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Top.thmBA_of_thmB_propA | exact GlobalTheory.CompanionTheory.Ar.Top.thmBA_of_thmB_propA | (intros; apply GlobalTheory.CompanionTheory.Ar.Top.thmBA_of_thmB_propA <;> assumption)
