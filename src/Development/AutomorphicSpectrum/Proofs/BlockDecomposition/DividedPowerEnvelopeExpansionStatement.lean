import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DividedPowerEnvelopeExpansion
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris DividedPowers GlobalTheory.PDA CrystallineSemistableComparison CrystallineSemistableComparison.Pb CrystallineSemistableComparison.Pb.Site
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.divided_power_envelope_expansion : ∀ {B : Type} [CommRing B] {J : Ideal B} (δ : DividedPowers J) (z : (pq B).P), ∃ b : ℕ →₀ B, z = b.sum fun k c => algebraMap B (pq B).P c * (eta δ).dpow k ((pq B).e 1) := by
  first | exact @GlobalTheory.CompanionTheory.PDSpanning.exists_sum_dpow | exact GlobalTheory.CompanionTheory.PDSpanning.exists_sum_dpow | (intros; apply GlobalTheory.CompanionTheory.PDSpanning.exists_sum_dpow <;> assumption)
