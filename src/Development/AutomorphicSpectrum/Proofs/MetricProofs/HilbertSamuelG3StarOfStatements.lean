import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.ExistsFormOfMemChartRingZ
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PTwistIntersectionInt
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PUnitApprox
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PConstantsRegular
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PConstantsDescend
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PChartConstantsDetermined
import Development.AutomorphicSpectrum.Proofs.MetricProofs.DegreeGenericOfDegree
import Development.AutomorphicSpectrum.Proofs.MetricProofs.DegreeOfIsIntersectionSystem
import Development.AutomorphicSpectrum.Proofs.MetricProofs.HilbertSamuelG3OfMoriwakiStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.EmbeddingPiecesOfIntersectionAndResolutionStatement

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry Filter Topology NumberField

namespace GlobalTheory.CompanionTheory.Ar.Giv

theorem hilbert_samuel_G3Star_of_systems :
    ReciprocityTheory.ChartRestriction.G.Geo.ArithIntersectionSystemStatement → ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.MoriwakiHSStatement →
      ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.MoriwakiBigStatement → ReciprocityTheory.ChartRestriction.G.Geo.ResK.ResKStatement →
      GroundTheory.Heights₂.Heights.HilbertSamuel.ArithmeticVolumeMultiplicative.Statement := by
  intro hSys hHS hBig hRes
  exact GroundTheory.Heights₂.Heights.HilbertSamuel.ArithmeticVolumeMultiplicative.proof (GlobalTheory.T.hilbert_samuel_G3_of_moriwaki hHS hBig)
    GroundTheory.Heights₂.Heights.HilbertSamuel.EmbeddingWeight.proof
    (GroundTheory.Heights₂.Heights.HilbertSamuel.TwistIntersectionInt.proof (GlobalTheory.T.embedding_pieces_of_intersection_and_resolution hSys hRes)
      (degreeGeneric_of_degree (degree_of_system hSys)))
    GroundTheory.Heights₂.Heights.HilbertSamuel.UnitApprox.proof
    (GroundTheory.Heights₂.Heights.HilbertSamuel.ConstantsRegular.proof
      GroundTheory.Heights₂.Heights.HilbertSamuel.ConstantsDescend.proof
      GroundTheory.Heights₂.Heights.HilbertSamuel.ChartConstantsDetermined.proof)

end GlobalTheory.CompanionTheory.Ar.Giv
