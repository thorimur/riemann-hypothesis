import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FiniteAlgebraAdelicLatticeProof
open GlobalTheory.RegSS
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finiteAlgebraAdelicLattice_proof : GlobalTheory.RegSS.TensorLattice := by
  first | exact @GlobalTheory.RegSSLattice.tensorLattice | exact GlobalTheory.RegSSLattice.tensorLattice | (intros; apply GlobalTheory.RegSSLattice.tensorLattice <;> assumption)
