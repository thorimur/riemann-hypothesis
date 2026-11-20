import Development.AutomorphicSpectrum.Proofs.MetricProofs.BallDomainOpenConvexZero
open NumberField Matrix MeasureTheory Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GroundTheory.Heights₂.Heights.FiniteCovolume GroundTheory.Automorphic GlobalTheory.CompanionTheory.Ar.Cusp.Dict
open scoped ENNReal InnerProductSpace
open scoped ComplexOrder

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ball_domain_open_convex_zero : ∀ (Ψ : Type) [Fintype Ψ] (j j' n : ℕ) (q : Ψ × Fin j × Fin j' ≃ Fin n), IsOpen (ballDom q) ∧ Convex ℝ (ballDom q) ∧ (0 : Fin n → ℂ) ∈ ballDom q := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Cusp.BallConvex.ballDom_open_convex_zero | exact GlobalTheory.CompanionTheory.Ar.Cusp.BallConvex.ballDom_open_convex_zero | (intros; apply GlobalTheory.CompanionTheory.Ar.Cusp.BallConvex.ballDom_open_convex_zero <;> assumption)
