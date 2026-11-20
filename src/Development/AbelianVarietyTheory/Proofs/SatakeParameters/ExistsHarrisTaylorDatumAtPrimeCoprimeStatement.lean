import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsHarrisTaylorDatumAtPrimeCoprime
open NumberField
open GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_harrisTaylorDatum_at_prime_coprime : ∀ (G : GDatum) (N : ℕ), 0 < N → ∃ (p : ℕ) (_ : Fact p.Prime) (D : Datum p), N.Coprime p ∧ D.toG = G := by
  first | (exact @GlobalTheory.GoodPrime.exists_datum) | (exact GlobalTheory.GoodPrime.exists_datum) | (intros; apply GlobalTheory.GoodPrime.exists_datum  <;> assumption)
