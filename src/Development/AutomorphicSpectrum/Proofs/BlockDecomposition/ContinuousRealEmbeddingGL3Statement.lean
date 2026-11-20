import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousRealEmbeddingGL3
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
theorem _root_.GlobalTheory.T.continuous_real_embedding_GL3 : Continuous GL2LocalData.emR := by
  first | exact @GlobalTheory.CompanionTheory.GL2Factorization.EmRCont.continuous_emR | exact GlobalTheory.CompanionTheory.GL2Factorization.EmRCont.continuous_emR | (intros; apply GlobalTheory.CompanionTheory.GL2Factorization.EmRCont.continuous_emR <;> assumption)
