import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InvariantDifferentialsConnectedPDivGroupCoordina
open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Katz
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.invariantDifferentials_connectedPDivGroup_coordinates : ∀ (p : ℕ) (k : Type) [CommRing k] (d : ℕ) (G : PDivGroup p k) (c : Chart G d), (∀ w : Fin d → k, (fun n => ∑ i, w i • dUnit k (c.x n i)) ∈ G.omegaSub) ∧ ∀ u : G.omega, ∃! w : Fin d → k, ∀ n, u.1 n = ∑ i, w i • dUnit k (c.x n i) := by
  first | exact @GlobalTheory.OmegaCoord.omega_coord | exact GlobalTheory.OmegaCoord.omega_coord | (intros; apply GlobalTheory.OmegaCoord.omega_coord <;> assumption)
