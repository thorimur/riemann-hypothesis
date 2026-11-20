import Development.AbelianVarietyTheory.Proofs.FoundationProofs.NablaDeltaOperatorLatticePreserved
open NumberField IsDedekindDomain MvPolynomial Formalism.BasicNotions Formalism.L2.DIV Formalism.DivisionValues GlobalTheory.TestLat Formalism.L2.Indef.Tree.ArchimedeanLeafBounds.Cuts
open scoped Matrix ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.nablaDeltaOperator_lattice_preserved : NabDelLattice := by
  first | exact @GlobalTheory.TransLattice.nabDelLattice | exact GlobalTheory.TransLattice.nabDelLattice | (intros; apply GlobalTheory.TransLattice.nabDelLattice <;> assumption)
