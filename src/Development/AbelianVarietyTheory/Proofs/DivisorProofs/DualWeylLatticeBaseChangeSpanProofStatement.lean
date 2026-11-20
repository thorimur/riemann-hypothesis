import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DualWeylLatticeBaseChangeSpanProof
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dualWeylLattice_baseChange_span_proof : GlobalTheory.BaseCmp.NabBaseChange := by
  first | exact @GlobalTheory.NabBC.nabBaseChange | exact GlobalTheory.NabBC.nabBaseChange | (intros; apply GlobalTheory.NabBC.nabBaseChange <;> assumption)
