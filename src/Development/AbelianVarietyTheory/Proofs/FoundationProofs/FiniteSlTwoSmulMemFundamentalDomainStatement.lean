import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FiniteSlTwoSmulMemFundamentalDomain
open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_slTwo_smul_mem_fundamentalDomain : ∀ τ : ℍ, {γ : SL(2, ℤ) | γ • τ ∈ ModularGroup.fd}.Finite := by
  first | exact @GlobalTheory.EisM.finite_smul_mem_fd | exact GlobalTheory.EisM.finite_smul_mem_fd | (intros; apply GlobalTheory.EisM.finite_smul_mem_fd <;> assumption)
