import Development.AutomorphicSpectrum.Proofs.GeometryProofs.GeometricallyConnectedBaseChangeIffFibers
open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open scoped CategoryTheory.Obj CategoryTheory.MonObj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.geometricallyConnected_baseChange_iff_fibers : ∀ (k V : Type) [CommRing k] [CommRing V] [Algebra k V] (X : Scheme.{0}) (p : X ⟶ Sp k), GeometricallyConnected (pullback.snd p (spMap (algebraMap k V))) ↔ ∀ x ∈ Set.range (PrimeSpectrum.comap (algebraMap k V)), GeometricallyConnected (pullback.snd p (spMap (algebraMap k x.asIdeal.ResidueField))) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Approx.geometricallyConnected_pullback_snd_spMap_iff_residueField | exact GlobalTheory.CompanionTheory.Ar.Approx.geometricallyConnected_pullback_snd_spMap_iff_residueField | (intros; apply GlobalTheory.CompanionTheory.Ar.Approx.geometricallyConnected_pullback_snd_spMap_iff_residueField <;> assumption)
