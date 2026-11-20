import Development.AbelianVarietyTheory.Proofs.SatakeParameters.KappaNormAtSplitPrimes
open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Ker Formalism.L2.Col Classical
open Formalism.L2.Th1.H (cmL CmOK matH IsIsom taylorMv)
open Formalism.L2.Th1.GD (LocNorm InMul frameM thetaLin)
open Formalism.L2.Th1.E (IntCurve curveL Unif)
open Formalism.DworkPowerSeriesWeights (JetsIntegral)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kappa_norm_at_splitPrimes : ∀ D : D7, KappaSplit D := by
  first | exact @GlobalTheory.kappaSplit_all | exact GlobalTheory.kappaSplit_all | (intros; apply GlobalTheory.kappaSplit_all <;> assumption)
