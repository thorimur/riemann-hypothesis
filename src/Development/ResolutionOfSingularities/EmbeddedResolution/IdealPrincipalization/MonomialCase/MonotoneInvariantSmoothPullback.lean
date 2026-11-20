import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MonomialCase.MonomialCenterSmoothPullback
universe u

open CategoryTheory AlgebraicGeometry

noncomputable section

namespace FunctorialResolution.EmbeddedResolution

namespace MonomialCenter

theorem IsComponentCompatiblePullback.of_flat (hGeom : MonomialGeometryHypotheses.{u}) (T : MarkedIdealWithBoundary.{u})
    (hT : T.IsAdmissible) (Y : Scheme.{u}) (k' : Type u) [Field k']
    (q : Y ⟶ Spec (CommRingCat.of k')) (g : Y ⟶ T.scheme) [AlgebraicGeometry.Flat g]
    (hT' : (T.pullbackOverField Y k' q g).IsAdmissible)
    (hord : ∀ (A : T.scheme.IdealSheafData) (y : ↥Y), orderAt (A.comap g) y = orderAt A (g y)) :
    IsComponentCompatiblePullback T Y k' q g :=
  ⟨fun J 𝒞 h𝒞 hop => hGeom.flat_comap_center T hT Y k' q g hT' J 𝒞 h𝒞 hop,
    fun J => hGeom.flat_components_down T hT Y k' q g hT' J,
    fun J => hGeom.flat_components_up T hT Y k' q g hT' J, hord⟩

end MonomialCenter

end FunctorialResolution.EmbeddedResolution

end
