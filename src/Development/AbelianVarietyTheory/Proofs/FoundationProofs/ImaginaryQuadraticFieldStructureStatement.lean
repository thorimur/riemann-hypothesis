import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ImaginaryQuadraticFieldStructure
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.GalTheta
open scoped BigOperators
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_orthonormal_frame_var : ∀ (D : D7) (N N' : ℕ), ∃ (m r : ℕ) (b : Fin r → Matrix (Fin N') (Fin (N + m)) D.host.E), OnB D b := by
  first | exact @GlobalTheory.FourCopies.exists_onB_four | exact GlobalTheory.FourCopies.exists_onB_four | (intros; apply GlobalTheory.FourCopies.exists_onB_four <;> assumption)
