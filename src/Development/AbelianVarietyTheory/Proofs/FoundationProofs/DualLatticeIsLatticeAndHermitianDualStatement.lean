import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DualLatticeIsLatticeAndHermitianDual
open NumberField IsDedekindDomain MvPolynomial Formalism.BasicNotions Formalism.L2.DIV Formalism.DivisionValues GlobalTheory.TestLat Formalism.L2.Indef.Tree.ArchimedeanLeafBounds.Cuts
open scoped Matrix ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dualLattice_isLattice_and_hermitianDual : DualFrLattice ∧ DualFrHdual := by
  first | exact @GlobalTheory.DualLat.dualFr_lattice_and_hdual | exact GlobalTheory.DualLat.dualFr_lattice_and_hdual | (intros; apply GlobalTheory.DualLat.dualFr_lattice_and_hdual <;> assumption)
