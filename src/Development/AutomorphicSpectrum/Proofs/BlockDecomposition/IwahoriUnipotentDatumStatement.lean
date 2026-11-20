import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IwahoriUnipotentDatum
open GlobalTheory.PRep GlobalTheory.SmGL Matrix Formalism.UG PositivityTheory.SphericalProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.iwahori_unipotent_datum : PositivityTheory.SphericalProduct.IwahoriU := by
  first | exact @GlobalTheory.CompanionTheory.IwUnit.iwahoriU | exact GlobalTheory.CompanionTheory.IwUnit.iwahoriU | (intros; apply GlobalTheory.CompanionTheory.IwUnit.iwahoriU <;> assumption)
