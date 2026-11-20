import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReduction.OrderUnderStalkIsomorphism
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.MarkedSequenceOfBlowups
universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace

namespace FunctorialResolution.EmbeddedResolution

theorem orderAt_comap_eq_of_notMem_exceptionalIdeal
    (T : MarkedIdealWithBoundary.{u}) (_hT : T.IsAdmissible) (Z : T.scheme.IdealSheafData)
    (X' : Scheme.{u}) (π : X' ⟶ T.scheme) (hπ : Blowup.IsBlowupAlongIdealSheaf π Z)
    (x' : X') (hx' : x' ∉ (Blowup.exceptionalIdeal π Z).support)
    (A : T.scheme.IdealSheafData) :
    orderAt (A.comap π) x' = orderAt A (π.base x') := by
  have hx : π.base x' ∉ Z.support := by
    intro hc
    apply hx'
    rw [Blowup.exceptionalIdeal_eq_comap]
    exact Scheme.IdealSheafData.mem_support_comap.mpr hc
  haveI : IsIso (π.stalkMap x') := isIso_stalkMap_of_isBlowupAlongIdealSheaf π Z hπ x' hx
  exact orderAt_comap_of_isIso_stalkMap π A x'

end FunctorialResolution.EmbeddedResolution
