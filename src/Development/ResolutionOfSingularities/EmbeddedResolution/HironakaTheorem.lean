import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.StrictNormalCrossingsClopen
import Development.ResolutionOfSingularities.EmbeddedResolution.StrongResolution.AffineCentersOverSingularLocus
import Development.ResolutionOfSingularities.EmbeddedResolution.StrongResolution.AffineBoundaryStrictNormalCrossings
import Development.ResolutionOfSingularities.EmbeddedResolution.StrongResolution.SingularPreimageBoundary
import Development.ResolutionOfSingularities.EmbeddedResolution.StrongResolution.GlobalResolutionFromAffine
import Development.ResolutionOfSingularities.EmbeddedResolution.StrongResolution.ClosedEmbeddingsIntoAffineSpace
universe u

open CategoryTheory AlgebraicGeometry

namespace FunctorialResolution.EmbeddedResolution

theorem isStrongResolution_canonicalAffineResolutionRule (k : Type u) [Field k] [CharZero k] (Y : Scheme.{u})
    (p : Y ⟶ Spec (CommRingCat.of k)) [AlgebraicGeometry.IsAffine Y]
    [AlgebraicGeometry.IsReduced Y] [AlgebraicGeometry.LocallyOfFiniteType p]
    [AlgebraicGeometry.QuasiCompact p] :
    IsStrongResolution k Y p (canonicalAffineResolutionRule k Y p) := by
  have hIso : EmbeddedPrincipalizationDiscardedLocusIsOpen principalizationWithRadicalCenters.{u} affineEmbedsIntoAffineSpace
      nilIsStrictNormalCrossingsOnAffineSpace affineSpaceIsSmooth :=
    embeddedPrincipalizationDiscardedLocusIsOpen_of_detachedLocusIsOpen principalizationWithRadicalCenters.{u}
      detachedLocusIsOpenForEmbeddings_principalizationWithRadicalCenters
  have hsmooth : AffineDetachedSmooth principalizationWithRadicalCenters.{u} affineEmbedsIntoAffineSpace
      nilIsStrictNormalCrossingsOnAffineSpace affineSpaceIsSmooth :=
    affineDetachedSmooth principalizationWithRadicalCenters.{u} affineEmbedsIntoAffineSpace
      nilIsStrictNormalCrossingsOnAffineSpace affineSpaceIsSmooth
  have hCen : AffineCentersLieOverSingularLocus principalizationWithRadicalCenters.{u} affineEmbedsIntoAffineSpace
      nilIsStrictNormalCrossingsOnAffineSpace affineSpaceIsSmooth embeddedPrincipalizationYieldsBlowups_principalizationWithRadicalCenters :=
    affineCentersLieOverSingularLocus_principalizationWithRadicalCenters
  show IsStrongResolution k Y p
    (affineResolutionRuleOfPrincipalization principalizationWithRadicalCenters.{u} affineEmbedsIntoAffineSpace
      nilIsStrictNormalCrossingsOnAffineSpace affineSpaceIsSmooth embeddedPrincipalizationYieldsBlowups_principalizationWithRadicalCenters k Y p)
  exact isStrongResolution_blowupSequenceWithoutIsos_ofAffine principalizationWithRadicalCenters.{u} affineEmbedsIntoAffineSpace
    nilIsStrictNormalCrossingsOnAffineSpace affineSpaceIsSmooth embeddedPrincipalizationYieldsBlowups_principalizationWithRadicalCenters
    (affineStrictTransformEmptyAtLast_of_isFunctorialPrincipalization principalizationWithRadicalCenters.{u}
      isFunctorialPrincipalization_principalizationWithRadicalCenters affineEmbedsIntoAffineSpace nilIsStrictNormalCrossingsOnAffineSpace
      affineSpaceIsSmooth)
    hsmooth
    (affineSmoothLocusPreimageDenseInDetached principalizationWithRadicalCenters.{u} affineEmbedsIntoAffineSpace
      nilIsStrictNormalCrossingsOnAffineSpace affineSpaceIsSmooth)
    hCen
    (affineDetachedClopenInCenter principalizationWithRadicalCenters.{u} affineEmbedsIntoAffineSpace
      nilIsStrictNormalCrossingsOnAffineSpace affineSpaceIsSmooth)
    (affineDetachedComponentsNotInBoundary principalizationWithRadicalCenters.{u} affineEmbedsIntoAffineSpace
      nilIsStrictNormalCrossingsOnAffineSpace affineSpaceIsSmooth)
    (affineDetachedSingularPreimageEqBoundary_of_centersLieOverSing principalizationWithRadicalCenters.{u} affineEmbedsIntoAffineSpace
      nilIsStrictNormalCrossingsOnAffineSpace affineSpaceIsSmooth hIso hsmooth
      embeddedPrincipalizationYieldsBlowups_principalizationWithRadicalCenters hCen)
    (affineCentersHaveStrictNormalCrossingsWithBoundary principalizationWithRadicalCenters.{u} affineEmbedsIntoAffineSpace
      nilIsStrictNormalCrossingsOnAffineSpace affineSpaceIsSmooth)
    (affineAllLevelsSmooth principalizationWithRadicalCenters.{u} affineEmbedsIntoAffineSpace
      nilIsStrictNormalCrossingsOnAffineSpace affineSpaceIsSmooth)
    (affineBoundaryInStrictNormalCrossingPosition principalizationWithRadicalCenters.{u} affineEmbedsIntoAffineSpace
      nilIsStrictNormalCrossingsOnAffineSpace affineSpaceIsSmooth)
    strictNormalCrossingsRestrictToClopen Blowup.blowupIsProper k Y p

theorem strongResolutionOfSingularitiesCharZero :
    StrongResolutionOfSingularitiesCharZero.{u} :=
  strongResolutionOfSingularitiesCharZero_of_principalizationAlgorithm principalizationWithRadicalCenters.{u}
    affineEmbedsIntoAffineSpace nilIsStrictNormalCrossingsOnAffineSpace affineSpaceIsSmooth
    isFunctorialPrincipalization_principalizationWithRadicalCenters
    transitionsAreBlowupsForEmbeddings_principalizationWithRadicalCenters
    embeddedPrincipalizationYieldsBlowups_principalizationWithRadicalCenters
    closedEmbeddingsRelatedByAutomorphism
    isStrongResolution_canonicalAffineResolutionRule

end FunctorialResolution.EmbeddedResolution
