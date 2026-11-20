import Development.AbelianVarietyTheory.Proofs.FoundationProofs.TransportedLatticeLocalizationFreeLeCoefficientS
open NumberField IsDedekindDomain MvPolynomial Formalism.BasicNotions Formalism.L2.DIV Formalism.DivisionValues GlobalTheory.TestLat Formalism.L2.Indef.Tree.ArchimedeanLeafBounds.Cuts
open scoped Matrix ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.transportedLattice_localization_free_le_coefficientSpace : NabDelLoc ∧ NabDelFree ∧ NabLeVV := by
  first | exact @GlobalTheory.TransLoc.nabDelLoc_free_leVV | exact GlobalTheory.TransLoc.nabDelLoc_free_leVV | (intros; apply GlobalTheory.TransLoc.nabDelLoc_free_leVV <;> assumption)
