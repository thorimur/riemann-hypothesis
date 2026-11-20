import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ZelevinskyGrothendieckPolynomialRingOfSegments
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.JHMult
theorem _root_.GlobalTheory.T.zelevinskyGrothendieckPolynomialRing_of_segments : GlobalTheory.Published.BernsteinZelevinskyFiniteness → GlobalTheory.Published.SegmentRepresentation → GlobalTheory.Published.GrothendieckRingPolynomial → GlobalTheory.Published.ZelevinskyPolynomialRing := by
  first | exact @GlobalTheory.zelevinskyPolynomialRing_of_parts | exact GlobalTheory.zelevinskyPolynomialRing_of_parts | (intros; apply GlobalTheory.zelevinskyPolynomialRing_of_parts <;> assumption)
