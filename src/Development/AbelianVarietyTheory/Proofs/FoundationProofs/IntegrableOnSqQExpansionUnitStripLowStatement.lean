import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IntegrableOnSqQExpansionUnitStripLow
open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integrableOn_sq_qExpansion_unitStrip_low : ∀ (e : ℕ) (b : ℕ → ℂ) (s : ℝ), 1 ≤ e → 0 < s → PolyB b → (Summable fun n : ℕ => ‖b n‖ ^ 2 / (n : ℝ) ^ (2 * (e : ℝ) - 1 + s)) → IntegrableOn (fun τ : ℍ => ‖qs b τ‖ ^ 2 * τ.im ^ (2 * (e : ℝ) + s)) {τ | τ ∈ strip ∧ τ.im < 1} := by
  first | exact @GlobalTheory.EisM.integrableOn_sq_qs_low | exact GlobalTheory.EisM.integrableOn_sq_qs_low | (intros; apply GlobalTheory.EisM.integrableOn_sq_qs_low <;> assumption)
