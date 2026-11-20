import Development.AbelianVarietyTheory.Proofs.FoundationProofs.TransportedWeylLatticeHermitianDuality
open NumberField IsDedekindDomain MvPolynomial Formalism.BasicNotions Formalism.L2.DIV Formalism.DivisionValues GlobalTheory.TestLat Formalism.L2.Indef.Tree.ArchimedeanLeafBounds.Cuts
open scoped Matrix ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.transported_weylLattice_hermitianDuality : NabDelDual := by
  first | exact @GlobalTheory.TransDual.nabDelDual | exact GlobalTheory.TransDual.nabDelDual | (intros; apply GlobalTheory.TransDual.nabDelDual <;> assumption)
