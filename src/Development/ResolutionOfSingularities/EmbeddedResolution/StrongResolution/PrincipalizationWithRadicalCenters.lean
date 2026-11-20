import Development.ResolutionOfSingularities.EmbeddedResolution.StrictTransformIsolation.StrictTransformAvoidance
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.ClosedEmbedding.ClosedImmersionCommutation
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.CanonicalRulesCorrect
import Development.ResolutionOfSingularities.EmbeddedResolution.StrongResolution.AffineEmbeddingIntoAffineSpace
universe u

open CategoryTheory AlgebraicGeometry

noncomputable section

namespace FunctorialResolution.EmbeddedResolution

theorem canonicalAlgorithmRules_isCorrect :
    (canonicalAlgorithmRules strictTransformIsBlowupOfClosedSubscheme.{u}).ReducesInductivelyOnDimension :=
  isCorrect_canonicalAlgorithmRules strictTransformIsBlowupOfClosedSubscheme

noncomputable abbrev principalizationWithRadicalCenters : PrincipalizationAlgorithm.{u} :=
  canonicalPrincipalization strictTransformIsBlowupOfClosedSubscheme smoothSubschemeIdealIsRadical.{u}

theorem embeddedPrincipalizationDiscardedLocusIsOpen_of_detachedLocusIsOpen (A : PrincipalizationAlgorithm.{u}) (h : DetachedLocusIsOpenForEmbeddings.{u} A) :
    EmbeddedPrincipalizationDiscardedLocusIsOpen.{u} A affineEmbedsIntoAffineSpace
      nilIsStrictNormalCrossingsOnAffineSpace affineSpaceIsSmooth := by
  intro k _ _ Y pY _ _ _ _ i hi
  exact h k Y pY
    (affineSpaceEmbeddingDatum affineEmbedsIntoAffineSpace nilIsStrictNormalCrossingsOnAffineSpace
      affineSpaceIsSmooth k Y pY) i hi

theorem chartIsolationHypotheses_principalizationWithRadicalCenters :
    OpenImmersionRestriction.ChartIsolationHypotheses OpenImmersionRestriction.vanishingIdealAssignment.{u} principalizationWithRadicalCenters.{u} := by
  have h : OpenImmersionRestriction.reducedVanishingAssignment.{u} = OpenImmersionRestriction.vanishingIdealAssignment.{u} := by
    funext X T
    rw [OpenImmersionRestriction.vanishingIdealAssignment_apply]
    rfl
  have h2 := OpenImmersionRestriction.chartIsolationHypotheses_reducedVanishingAssignment principalizationWithRadicalCenters.{u}
  rwa [h] at h2

theorem detachedLocusIsOpenForEmbeddings_principalizationWithRadicalCenters :
    DetachedLocusIsOpenForEmbeddings.{u} principalizationWithRadicalCenters.{u} :=
  OpenImmersionRestriction.detachedLocusIsOpenForEmbeddings_canonicalPrincipalization OpenImmersionRestriction.idealSheafGeometryHypotheses_vanishingIdealAssignment.{u}
    strictTransformIsBlowupOfClosedSubscheme.{u} canonicalAlgorithmRules_isCorrect smoothSubschemeIdealIsRadical.{u}
    chartIsolationHypotheses_principalizationWithRadicalCenters.{u}

theorem transitionsAreBlowupsForEmbeddings_principalizationWithRadicalCenters :
    TransitionsAreBlowupsForEmbeddings principalizationWithRadicalCenters.{u} :=
  transitionsAreBlowupsForEmbeddings_of_detachedLocusIsOpen principalizationWithRadicalCenters.{u}
    detachedLocusIsOpenForEmbeddings_principalizationWithRadicalCenters

theorem embeddedPrincipalizationYieldsBlowups_principalizationWithRadicalCenters :
    EmbeddedPrincipalizationYieldsBlowups principalizationWithRadicalCenters.{u} affineEmbedsIntoAffineSpace
      nilIsStrictNormalCrossingsOnAffineSpace affineSpaceIsSmooth :=
  embeddedPrincipalizationYieldsBlowups_of_discardedLocusIsOpen principalizationWithRadicalCenters.{u} affineEmbedsIntoAffineSpace
    nilIsStrictNormalCrossingsOnAffineSpace affineSpaceIsSmooth
    (embeddedPrincipalizationDiscardedLocusIsOpen_of_detachedLocusIsOpen principalizationWithRadicalCenters.{u}
      detachedLocusIsOpenForEmbeddings_principalizationWithRadicalCenters)
    (embeddedPrincipalizationAmbientIsNoetherian principalizationWithRadicalCenters.{u} affineEmbedsIntoAffineSpace
      nilIsStrictNormalCrossingsOnAffineSpace affineSpaceIsSmooth)
    strictTransformIsBlowupOfClosedSubscheme

theorem isFunctorialPrincipalization_principalizationWithRadicalCenters : IsFunctorialPrincipalization principalizationWithRadicalCenters.{u} :=
  isFunctorialPrincipalization_canonicalPrincipalization strictTransformIsBlowupOfClosedSubscheme canonicalAlgorithmRules_isCorrect
    smoothSubschemeIdealIsRadical
    (commutesWithClosedImmersion_of_isCorrect (canonicalAlgorithmRules strictTransformIsBlowupOfClosedSubscheme) canonicalAlgorithmRules_isCorrect)

noncomputable def canonicalAffineResolutionRule : AffineResolutionRule.{u} :=
  affineResolutionRuleOfPrincipalization principalizationWithRadicalCenters.{u} affineEmbedsIntoAffineSpace
    nilIsStrictNormalCrossingsOnAffineSpace affineSpaceIsSmooth embeddedPrincipalizationYieldsBlowups_principalizationWithRadicalCenters

end FunctorialResolution.EmbeddedResolution
