import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GroupStructureOfHyp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.group_structure_of_published_inputs : GlobalTheory.Published.RaynaudExtension → GlobalTheory.Published.GrothendieckOrthogonality → GlobalTheory.Published.DualAbelianScheme → GlobalTheory.Published.CubeTheorem → GlobalTheory.GroupBplus.GroupSt := by
  first | exact @GlobalTheory.GroupBplus.groupSt | exact GlobalTheory.GroupBplus.groupSt | (intros; apply GlobalTheory.GroupBplus.groupSt <;> assumption)
