import Development.AutomorphicSpectrum.Proofs.MetricProofs.HilbertSamuelG7OfMoriwakiStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.PackingStatement
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry Filter Topology NumberField

namespace GlobalTheory.CompanionTheory.Ar.Giv

theorem selfIntersection_le_of_boundedInjection :
    MoriwakiHSStatement → MoriwakiBigStatement → GroundTheory.Heights₂.Heights.HilbertSamuel.G3.Statement :=
  fun hHS hBig =>
    GroundTheory.Heights₂.Heights.HilbertSamuel.G3.proof
      GroundTheory.Heights₂.Heights.HilbertSamuel.LocalRep.proof
      GroundTheory.Heights₂.Heights.HilbertSamuel.ConstantShift.proof
      (GroundTheory.Heights₂.Heights.HilbertSamuel.ArithmeticVolumeBig.of_moriwakiBig_only hBig)
      (GlobalTheory.T.hilbert_samuel_G7_of_moriwaki hHS) GlobalTheory.T.packing'

end GlobalTheory.CompanionTheory.Ar.Giv
