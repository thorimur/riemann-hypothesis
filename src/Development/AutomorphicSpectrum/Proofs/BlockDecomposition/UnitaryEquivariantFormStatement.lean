import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnitaryEquivariantForm
open GlobalTheory.PRep Formalism.UG GlobalTheory.LFun PositivityTheory.SphericalProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitary_equivariant_form : PositivityTheory.SphericalProduct.EqFormU := by
  first | exact @GlobalTheory.CompanionTheory.EqForm.eqFormU | exact GlobalTheory.CompanionTheory.EqForm.eqFormU | (intros; apply GlobalTheory.CompanionTheory.EqForm.eqFormU <;> assumption)
