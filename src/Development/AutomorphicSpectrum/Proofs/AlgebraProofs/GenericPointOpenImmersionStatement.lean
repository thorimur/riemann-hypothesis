import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.GenericPointOpenImmersion

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj CategoryTheory.MonObj
open GlobalTheory.CechPic GlobalTheory.AbDual
open GlobalTheory.IndefiniteRowSideFullHecke.ZeroSectionBase (IsPrincipalPol sqToBase)
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.generic_point_open_immersion : ∀ (C : Type) [Field C] (R : Type) [CommRing R] [IsDomain R] [ValuationRing R] [Ring.DimensionLEOne R]
    [Algebra R C] [IsFractionRing R C], IsOpenImmersion (spMap (algebraMap R C)) := by
  first | exact @GlobalTheory.CompanionTheory.ValGeneric.isOpenImmersion_spMap_fraction | exact GlobalTheory.CompanionTheory.ValGeneric.isOpenImmersion_spMap_fraction | (intros; apply GlobalTheory.CompanionTheory.ValGeneric.isOpenImmersion_spMap_fraction <;> assumption)
