import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.StabSelfDualLatticeTransitiveOnLength
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.stabSelfDualLattice_transitive_on_length : GlobalTheory.IndefiniteRowSideFullHecke.SelfDualLatticeStabilizers.StabTransitive := by
  first | exact @GlobalTheory.StabOrbit.stabTransitive | exact GlobalTheory.StabOrbit.stabTransitive | (intros; apply GlobalTheory.StabOrbit.stabTransitive <;> assumption)
