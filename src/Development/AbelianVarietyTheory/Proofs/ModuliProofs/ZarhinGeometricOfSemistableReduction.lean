import Development.AbelianVarietyTheory.Proofs.ModuliProofs.UniformisationExistenceAndTorsionStatements
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.SemiAbelianSchemeUniformisationExistsGeometricStatement
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

namespace GlobalTheory

theorem zhGeo_of_semistableReduction :
    GlobalTheory.Published.SemistableReductionSt → GlobalTheory.ZH.ZHGeoSt := fun S => by
  obtain ⟨L, L2, L3, L4, L5, -⟩ := GlobalTheory.allSixLaws
  exact GlobalTheory.T.semiAbelianScheme_uniformisation_exists_geometric GlobalTheory.homExtension_semiAbelian_dvr S GlobalTheory.ZH.thmU_and_uTors.1 L L2 L3 L4 L5
    GlobalTheory.ZH.thmU_and_uTors.2

end GlobalTheory
