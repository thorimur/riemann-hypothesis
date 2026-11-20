import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.EtaleOverIntegersLocalization
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Points GlobalTheory.ArInt GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.ProjSpace GlobalTheory.CompanionTheory.Ar.BaseZ GlobalTheory.CompanionTheory.Ar.BGS
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.etale_over_integers_localization : ∀ (k : Type) [CommRing k] [IsDomain k] [CharZero k] [Module.Finite ℤ k], ∃ N : ℕ, N ≠ 0 ∧ (Int.castRingHom (Localization.Away (N : k))).Etale := by
  first | exact @GlobalTheory.CompanionTheory.CommAlg.OrderEtale.exists_etale_away | exact GlobalTheory.CompanionTheory.CommAlg.OrderEtale.exists_etale_away | (intros; apply GlobalTheory.CompanionTheory.CommAlg.OrderEtale.exists_etale_away <;> assumption)
