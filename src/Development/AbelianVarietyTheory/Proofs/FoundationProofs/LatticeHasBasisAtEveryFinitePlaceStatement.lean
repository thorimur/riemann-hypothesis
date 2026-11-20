import Development.AbelianVarietyTheory.Proofs.FoundationProofs.LatticeHasBasisAtEveryFinitePlace
open NumberField IsDedekindDomain MvPolynomial Formalism.BasicNotions Formalism.L2.DIV Formalism.DivisionValues GlobalTheory.TestLat Formalism.L2.Indef.Tree.ArchimedeanLeafBounds.Cuts
open scoped Matrix ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lattice_has_basis_at_every_finite_place : BasisAtEx := by
  first | exact @GlobalTheory.LatBasisAt.basisAtEx | exact GlobalTheory.LatBasisAt.basisAtEx | (intros; apply GlobalTheory.LatBasisAt.basisAtEx <;> assumption)
