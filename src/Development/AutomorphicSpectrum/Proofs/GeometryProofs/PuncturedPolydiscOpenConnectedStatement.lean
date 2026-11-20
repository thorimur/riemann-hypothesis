import Development.AutomorphicSpectrum.Proofs.GeometryProofs.PuncturedPolydiscOpenConnected
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat Filter Topology Metric
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.punctured_polydisc_open_connected : ∀ (n a : ℕ) (ρ : ℝ), 0 < ρ → IsOpen (punct n a ρ) ∧ IsPreconnected (punct n a ρ) ∧ (punct n a ρ).Nonempty := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Flat.PunctShape.punct_open_connected_nonempty | exact GlobalTheory.CompanionTheory.Ar.Flat.PunctShape.punct_open_connected_nonempty | (intros; apply GlobalTheory.CompanionTheory.Ar.Flat.PunctShape.punct_open_connected_nonempty <;> assumption)
