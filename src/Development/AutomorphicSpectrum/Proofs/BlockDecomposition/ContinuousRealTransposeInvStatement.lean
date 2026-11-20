import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousRealTransposeInv
open NumberField IsDedekindDomain MeasureTheory Matrix Filter Topology
open GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.GodementSection (localChar)
open GroundTheory.Automorphic.Reduction (finAt infAt maxCompact)
open GroundTheory.Automorphic.GLnLocal (integralGL)
open GroundTheory.Global.AdicLiesOver
open Ad3 Ad3.K Ad3.K.QuadraticBaseChangeGL3
open Ad3.R (G2 Jd md KA lc)
open scoped NumberField.AdeleRing ValuativeRel
open GlobalTheory.CompanionTheory.GL2Factorization
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.continuous_real_transposeInv : ∀ m : ℕ, Continuous (GL2LocalData.tinvR : GL (Fin m) ℝ → GL (Fin m) ℝ) := by
  first | exact @GlobalTheory.CompanionTheory.GL2Factorization.CtIn.tinvR_continuous | exact GlobalTheory.CompanionTheory.GL2Factorization.CtIn.tinvR_continuous | (intros; apply GlobalTheory.CompanionTheory.GL2Factorization.CtIn.tinvR_continuous <;> assumption)
