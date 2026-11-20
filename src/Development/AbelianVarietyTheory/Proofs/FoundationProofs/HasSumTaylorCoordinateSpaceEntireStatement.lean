import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HasSumTaylorCoordinateSpaceEntire
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.ThetaConj
open scoped BigOperators
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hasSum_taylor_coordinateSpace_entire : ∀ (D : D7) (N N' : ℕ) (F : VC D N N' → ℂ), Differentiable ℂ F → ∀ z : VC D N N', HasSum (fun α : Mono D N N' => taylor D F α * mono D α z) (F z) := by
  first | exact @GlobalTheory.EntireTaylor.hasSum_taylor_mono | exact GlobalTheory.EntireTaylor.hasSum_taylor_mono | (intros; apply GlobalTheory.EntireTaylor.hasSum_taylor_mono <;> assumption)
