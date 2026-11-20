import GroundTheory.HeightsAndTheta.Heights.HeightComparison.HeightAssemblyFull
import GroundTheory.HeightsAndTheta.Heights.HeightComparison.PCentredPlacesFinite
import GroundTheory.HeightsAndTheta.Heights.HeightComparison.PCentredRingNormal
import GroundTheory.HeightsAndTheta.Heights.HeightComparison.PLocalLengthPlaces
import GroundTheory.HeightsAndTheta.Heights.HeightComparison.PLocalNormalIndex
import GroundTheory.HeightsAndTheta.Heights.HeightComparison.POrbitCenterChart
import GroundTheory.HeightsAndTheta.Heights.HeightComparison.POrbitCenterDivSupp
import GroundTheory.HeightsAndTheta.Heights.HeightComparison.POrbitCenterLe
import GroundTheory.HeightsAndTheta.Heights.HeightComparison.POrbitCenterPrime
import GroundTheory.HeightsAndTheta.Heights.HeightComparison.POrbitCenterZero
import GroundTheory.HeightsAndTheta.Heights.HeightComparison.POrbitChartDehom
import GroundTheory.HeightsAndTheta.Heights.HeightComparison.POrbitChartMult
import GroundTheory.HeightsAndTheta.Heights.HeightComparison.POrbitChartRing
import GroundTheory.HeightsAndTheta.Heights.HeightComparison.POrbitChartTerm
import GroundTheory.HeightsAndTheta.Heights.HeightComparison.POrbitConjSum
import GroundTheory.HeightsAndTheta.Heights.HeightComparison.POrbitDegreeRatio
import GroundTheory.HeightsAndTheta.Heights.HeightComparison.POrbitLocalSum
import GroundTheory.HeightsAndTheta.Heights.HeightComparison.PPlaceCentredSum
import GroundTheory.HeightsAndTheta.Heights.HeightComparison.PPlacesRingQuot

namespace CoverDenseAlt
open GroundTheory.Heights₂.Heights

theorem heightRecR_full : HeightRecR.Statement :=
  have hM : OrbitChartMax.Statement := OrbitChartMax.proof
  have hQ : OrbitChartQuot.Statement := OrbitChartQuot.proof
  have hIff : OrbitCenterMemIff.Statement := OrbitCenterMemIff.proof
  HeightRecR.proof OrbitDivVertical.proof
    (OrbitFiniteSum.proof OrbitDegreeRatio.proof
      (OrbitLocalSum.proof OrbitChartRing.proof hM
        (OrbitChartResidue.proof hM hQ (OrbitChartDehom.proof hM hQ))
        OrbitChartMult.proof
        (LocalLengthPlaces.proof LocalQuotCard.proof CentredPlacesFinite.proof
          (LocalQuotCentred.proof CentredRingNormal.proof LocalNormalIndex.proof) PlacesRingQuot.proof)
        OrbitCenterChart.proof PlaceCentredSum.proof OrbitChartTerm.proof)
      (OrbitCenterZero.proof OrbitCenterLe.proof hIff
        (OrbitCenterDivSupp.proof hIff (OrbitCenterPrime.proof hIff) SubringPrimeMaximal.proof)))
    (OrbitArchSum.of_conjSum OrbitConjSum.proof)

theorem chartDehom_full : OrbitChartDehom.Statement :=
  OrbitChartDehom.proof OrbitChartMax.proof OrbitChartQuot.proof

end CoverDenseAlt
