import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ChartOpenMemCoverOfO1
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris ReciprocityTheory.ChartRestriction.G.Geo.Tor CrystallineSemistableComparison CrystallineSemistableComparison.Pb
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.chart_open_mem_cover_of_O1 : ∀ {K : Type} [Field K] {X : Scheme.{0}} (D : E.LineData X) (N : ℕ) (i : X ⟶ PSpace K N),
    IsTautologicalLineAt D N i → ∀ j, wch i j ∈ 𝒱D D := by
  first | exact @GlobalTheory.CompanionTheory.ConeWchMem.main | exact GlobalTheory.CompanionTheory.ConeWchMem.main | (intros; apply GlobalTheory.CompanionTheory.ConeWchMem.main <;> assumption)
