import Development.AbelianVarietyTheory.Proofs.SatakeParameters.NonemptyCoefficientFieldEmbeddingPadicComplex
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.nonempty_coefficient_field_embedding_padic_complex : ∀ (p : ℕ) [Fact p.Prime] (G : Formalism.MainNotions.G.GAtP p), 0 < G.P.nV → Nonempty (Formalism.L2.G.Pend.CEmb G) := by
  first | exact @GlobalTheory.nonempty_cEmb_of_pos_nV | exact GlobalTheory.nonempty_cEmb_of_pos_nV | (intros; apply GlobalTheory.nonempty_cEmb_of_pos_nV <;> assumption)
