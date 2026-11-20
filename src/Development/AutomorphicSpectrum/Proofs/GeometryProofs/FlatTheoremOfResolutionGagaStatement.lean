import Development.AutomorphicSpectrum.Proofs.GeometryProofs.FlatTheoremOfResolutionGaga
open CategoryTheory AlgebraicGeometry NumberField GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.HT GlobalTheory.CompanionTheory.Ar.Flat ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flat_theorem_of_resolution_gaga : Geo.ResK.ResKStatement → GagaSections → PartI → ThmFlatA := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Flat.thmFlatA_of_resK_gaga_partI | exact GlobalTheory.CompanionTheory.Ar.Flat.thmFlatA_of_resK_gaga_partI | (intros; apply GlobalTheory.CompanionTheory.Ar.Flat.thmFlatA_of_resK_gaga_partI <;> assumption)
