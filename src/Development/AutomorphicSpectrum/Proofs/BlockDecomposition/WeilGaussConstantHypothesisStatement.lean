import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WeilGaussConstantHypothesis
open MeasureTheory Matrix GroundTheory.LocalField GroundTheory.Automorphic Ad3 Ad3.K.GL2LocalData
open scoped ValuativeRel
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weil_gauss_constant_hypothesis : Ad3.K.GL2LocalData.WGaussLam := by
  first | exact @GlobalTheory.CompanionTheory.GaussLam.wGaussLam | exact GlobalTheory.CompanionTheory.GaussLam.wGaussLam | (intros; apply GlobalTheory.CompanionTheory.GaussLam.wGaussLam <;> assumption)
