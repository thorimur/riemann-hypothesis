import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnitaryJacquetNonzero
open GlobalTheory.PRep Formalism.UG GlobalTheory.LFun PositivityTheory.SphericalProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitary_jacquet_nonzero : PositivityTheory.SphericalProduct.JacNeU := by
  first | exact @GlobalTheory.CompanionTheory.JacSph.jacNeU | exact GlobalTheory.CompanionTheory.JacSph.jacNeU | (intros; apply GlobalTheory.CompanionTheory.JacSph.jacNeU <;> assumption)
