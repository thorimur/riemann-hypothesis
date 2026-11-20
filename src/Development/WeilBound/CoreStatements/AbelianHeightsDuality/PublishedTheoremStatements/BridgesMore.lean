import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsSqIntCoeffOfIsSquareIntegrable
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CuspTraceClassOfFactorisation
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ZelevinskyGrothendieckPolynomialRingOfSegmentsStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ToroidalChartsForFanOfToroidalForFanKS

namespace PositivityTheory.Prw

theorem squareIntegrableSegment_of (h : GlobalTheory.Published.EssSquareIntegrableSegments) : GlobalTheory.Published.SquareIntegrableSegment :=
  GlobalTheory.Published.squareIntegrableSegment_of_ess h

theorem cuspTraceClass_of (h : GlobalTheory.Published.DixmierMalliavinFactorisation) : GlobalTheory.Published.CuspTraceClass :=
  GlobalTheory.Published.cuspTraceClass_of_factorisation h

theorem zelevinskyPolynomialRing_of (h₁ : GlobalTheory.Published.BernsteinZelevinskyFiniteness) (h₂ : GlobalTheory.Published.SegmentRepresentation)
    (h₃ : GlobalTheory.Published.GrothendieckRingPolynomial) : GlobalTheory.Published.ZelevinskyPolynomialRing :=
  GlobalTheory.T.zelevinskyGrothendieckPolynomialRing_of_segments h₁ h₂ h₃

theorem toroidalChartsForFan_of (h : GlobalTheory.Published.ToroidalForFanKS) : GlobalTheory.Published.ToroidalChartsForFan :=
  GlobalTheory.toroidalChartsForFan_of_toroidalForFanKS h

end PositivityTheory.Prw
