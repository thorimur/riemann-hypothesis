import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.CmHostRankBounds
open AlgebraicGeometry CategoryTheory NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Top
open GroundTheory.Heights₂.Heights.LowerBoundFree (ComponentData ComponentSetting degMu ArLimExists slX)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cm_host_rank_bounds : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E), 2 ≤ hostRd E ∧ Nonempty (CMType H) ∧ 2 * Fintype.card (CMType H) = Module.finrank ℚ E := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Top.HostNumbers.host_numbers | exact GlobalTheory.CompanionTheory.Ar.Top.HostNumbers.host_numbers | (intros; apply GlobalTheory.CompanionTheory.Ar.Top.HostNumbers.host_numbers <;> assumption)
