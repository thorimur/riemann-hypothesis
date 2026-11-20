import Development.AbelianVarietyTheory.Proofs.FoundationProofs.LatticeExtensionAlongFieldEmbeddingDuals
open NumberField IsDedekindDomain MvPolynomial Formalism.BasicNotions Formalism.L2.DIV Formalism.DivisionValues GlobalTheory.TestLat Formalism.L2.Indef.Tree.ArchimedeanLeafBounds.Cuts
open scoped Matrix ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lattice_extension_along_field_embedding_duals : TauLatLattice ∧ TauLatDual ∧ RoundLat := by
  first | exact @GlobalTheory.TauLat.tauLat_lattice_dual_round | exact GlobalTheory.TauLat.tauLat_lattice_dual_round | (intros; apply GlobalTheory.TauLat.tauLat_lattice_dual_round <;> assumption)
