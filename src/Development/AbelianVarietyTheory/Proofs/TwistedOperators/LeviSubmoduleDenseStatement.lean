import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LeviSubmoduleDense
open MeasureTheory Matrix Filter Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.FlagMeas GlobalTheory.GKModule GlobalTheory.RealInd GlobalTheory.OpTrace
open GlobalTheory.SmoothGlob (lieSet)
open GlobalTheory.Dec (IsHaarSub HasInfChar IsSqIntIrr)
open GlobalTheory.Orb (ujMat ujRep CcMat IsBiFinite IsUnitEquiv IsCharFn IsRegSS cent HasOrbInt quotMeas)
open GlobalTheory.AutomorphicL2Unitary (IsTopIrreducible)
open GlobalTheory.HCChar GlobalTheory.Published GlobalTheory.Published.Langlands
open scoped InnerProductSpace Topology ENNReal ComplexConjugate
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.levi_submodule_dense : GlobalTheory.Published.IrreducibleUnitaryAdmissible → GlobalTheory.Published.KFiniteCoefficientsAnalytic → GlobalTheory.Published.LeviSubmoduleDense := by
  first | exact @GlobalTheory.LeviDense.leviSubmoduleDense | exact GlobalTheory.LeviDense.leviSubmoduleDense | (intros; apply GlobalTheory.LeviDense.leviSubmoduleDense <;> assumption)
