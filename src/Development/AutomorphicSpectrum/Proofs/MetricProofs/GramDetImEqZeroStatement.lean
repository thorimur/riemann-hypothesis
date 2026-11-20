import Development.AutomorphicSpectrum.Proofs.MetricProofs.GramDetImEqZero
open NumberField Matrix Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp GroundTheory.Heights₂.Heights.LowerBoundFree GroundTheory.Heights₂.Heights.Regular
open GlobalTheory.CompanionTheory.Ar.RiemannLimit GlobalTheory.CompanionTheory.Ar.Cusp.BoundaryLimit
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.gram_det_im_eq_zero : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (g : ℕ) (Λ : Type) [AddCommGroup Λ] [Module (𝓞 E) Λ] (R : RiemLat E g Λ) (m : ℕ) (u : Fin m → Fin g → ℂ), (R.gram u).det.im = 0 := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Cusp.GramReal.gram_det_im_zero | exact GlobalTheory.CompanionTheory.Ar.Cusp.GramReal.gram_det_im_zero | (intros; apply GlobalTheory.CompanionTheory.Ar.Cusp.GramReal.gram_det_im_zero <;> assumption)
