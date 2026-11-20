import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsModuliSchemePolarizedAbelianLevel
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_moduli_scheme_polarized_abelian_level : N1ab := by
  first | exact @GlobalTheory.Moduli.moduli_scheme_exists | exact GlobalTheory.Moduli.moduli_scheme_exists | (intros; apply GlobalTheory.Moduli.moduli_scheme_exists <;> assumption)
