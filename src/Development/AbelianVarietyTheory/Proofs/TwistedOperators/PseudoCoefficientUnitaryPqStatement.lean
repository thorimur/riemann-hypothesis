import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PseudoCoefficientUnitaryPq
open MeasureTheory Matrix Filter Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.FlagMeas GlobalTheory.GKModule GlobalTheory.RealInd GlobalTheory.OpTrace
open GlobalTheory.SmoothGlob (lieSet)
open GlobalTheory.Dec (IsHaarSub HasInfChar IsSqIntIrr)
open GlobalTheory.Orb (ujMat ujRep CcMat IsBiFinite IsUnitEquiv IsCharFn IsRegSS cent HasOrbInt quotMeas)
open GlobalTheory.AutomorphicL2Unitary (IsTopIrreducible)
open GlobalTheory.HCChar GlobalTheory.Published GlobalTheory.Published.Langlands
open scoped InnerProductSpace Topology ENNReal ComplexConjugate
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pseudo_coefficient_unitary_pq : GlobalTheory.Published.IrreducibleUnitaryAdmissible → GlobalTheory.Published.KFiniteCoefficientsAnalytic → GlobalTheory.Published.CharacterRegularityFiniteLength → GlobalTheory.Published.PseudoCoefficientExistence → GlobalTheory.Published.CuspidalOrbitalIntegrals → GlobalTheory.Published.PseudoCoefficientUpq := by
  first | exact @GlobalTheory.Published.pseudoCoefficientUpq_of_hypotheses | exact GlobalTheory.Published.pseudoCoefficientUpq_of_hypotheses | (intros; apply GlobalTheory.Published.pseudoCoefficientUpq_of_hypotheses <;> assumption)
