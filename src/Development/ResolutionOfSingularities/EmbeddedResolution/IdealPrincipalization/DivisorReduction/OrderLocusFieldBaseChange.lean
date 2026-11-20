import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.DerivativeIdealSheafFieldBaseChange
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DivisorReduction.FieldBaseChangeCompatibility
universe u

open CategoryTheory AlgebraicGeometry

namespace FunctorialResolution.EmbeddedResolution

theorem orderAtLeastLocus_withBoundary_baseChange_eq_preimage (T : MarkedIdealWithBoundary.{u}) (hV : T.IsAdmissible)
    (K : Type u) [Field K] (f : T.base →+* K)
    (E' : List (T.baseChange K f).scheme.IdealSheafData) (m : ℕ) :
    orderAtLeastLocus ((T.baseChange K f).withBoundary E').ideal m =
      (fieldBaseChangeProjection T K f) ⁻¹' orderAtLeastLocus T.ideal m := by
  haveI : CharZero T.base := hV.charZero
  haveI : CharZero K := (RingHom.charZero_iff f.injective).mp hV.charZero
  haveI : AlgebraicGeometry.Smooth T.structMap := hV.smooth
  exact orderAtLeastLocus_comap_fieldBaseChange T.structMap (CommRingCat.ofHom f) T.ideal m

end FunctorialResolution.EmbeddedResolution
