import Development.AbelianVarietyTheory.Proofs.SatakeParameters.NullNegEvalOfJacobianDetEqZero
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.null_negEval_of_jacobian_det_eq_zero : ∀ (X : Scheme.{0}) (p : X ⟶ Sp ℂ) (d : ℕ) (U : X.Opens) (ch : GlobalTheory.AlgChart p (RingHom.id ℂ) d)
    (φ : Fin d → Γ(X, U)), ∃ E : Set (Fin d → ℂ), MeasureTheory.volume E = 0 ∧
      ∀ z ∈ ch.e.source, ∀ hz : z ∈ GlobalTheory.CxPts.ptsIn p (RingHom.id ℂ) U,
        (ch.jacMat φ z).det = 0 → (fun j => -GlobalTheory.CxPts.evHom hz (φ j)) ∈ E := by
  first | (exact @GlobalTheory.ChartSard.null_negEv_of_det_eq_zero) | (exact GlobalTheory.ChartSard.null_negEv_of_det_eq_zero) | (intros; apply GlobalTheory.ChartSard.null_negEv_of_det_eq_zero  <;> assumption)
