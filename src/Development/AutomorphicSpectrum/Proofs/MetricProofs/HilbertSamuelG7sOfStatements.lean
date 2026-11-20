import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.SmallSectionCountLeOfIntegralMul
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PTwistMetric
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PTwistIntersectionAnyDegree
import Development.AutomorphicSpectrum.Proofs.MetricProofs.DegreeGenericOfDegree
import Development.AutomorphicSpectrum.Proofs.MetricProofs.DegreeOfIsIntersectionSystem
import Development.AutomorphicSpectrum.Proofs.MetricProofs.EmbeddingPiecesOfIntersectionAndResolutionStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.HodgeIndexImpliesHeightBoundStatement

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry Filter Topology NumberField

namespace GlobalTheory.CompanionTheory.Ar.Giv

theorem smallSections_upper_of_moriwaki :
    ReciprocityTheory.ChartRestriction.G.Geo.ArithIntersectionSystemStatement → ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.MoriwakiHSStatement →
      ReciprocityTheory.ChartRestriction.G.Geo.ResK.ResKStatement → ArithmeticHilbertSamuelUpperBoundNumberField := by
  intro hAIS hHS hRes
  have hDG : GroundTheory.Heights₂.Heights.Inter.DegreeGeneric.Statement :=
    degreeGeneric_of_degree (degree_of_system hAIS)
  have a0 := GroundTheory.Heights₂.Heights.HilbertSamuel.TwistIntersectionAnyDegree.proof (GlobalTheory.T.embedding_pieces_of_intersection_and_resolution hAIS hRes) hDG
  have a1 := GroundTheory.Heights₂.Heights.HilbertSamuel.TwistMetric.proof
    GroundTheory.Heights₂.Heights.HilbertSamuel.EmbeddingWeight.proof a0
  exact GroundTheory.Heights₂.Heights.HilbertSamuel.ArithmeticVolumeNefDual.proof (GlobalTheory.T.hodge_index_implies_height_bound hHS) GlobalTheory.T.packing'
    GroundTheory.Heights₂.Heights.HilbertSamuel.UnitApprox.proof
    GroundTheory.Heights₂.Heights.HilbertSamuel.NonvanishingDense.full a1

end GlobalTheory.CompanionTheory.Ar.Giv
