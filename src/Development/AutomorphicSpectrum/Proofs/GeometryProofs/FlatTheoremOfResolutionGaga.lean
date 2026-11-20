import Development.AutomorphicSpectrum.Proofs.GeometryProofs.FlatZeroFromResolutionAndGagaStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.FlatFirstFromResolutionAndGagaStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.FiniteConstantHoldsStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.FlatTheoremOfPartsStatement

open CategoryTheory AlgebraicGeometry NumberField GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.HT GlobalTheory.CompanionTheory.Ar.Flat ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.CompanionTheory.Ar.Flat

theorem thmFlatA_of_resK_gaga_partI :
    Geo.ResK.ResKStatement → GagaSections → PartI → ThmFlatA :=
  fun hR hG hP =>
    GlobalTheory.T.flat_theorem_of_parts hP (GlobalTheory.T.flat_zero_from_resolution_and_gaga hR hG) (GlobalTheory.T.flat_first_from_resolution_and_gaga hR hG) GlobalTheory.T.finite_constant_holds

end GlobalTheory.CompanionTheory.Ar.Flat
