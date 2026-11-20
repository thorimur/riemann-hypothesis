import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CuspidalGLLocalComponentsEventuallySatake
open NumberField IsDedekindDomain Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.ContraPair
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cuspidal_GL_local_components_eventually_satake : GlobalTheory.Published.AutomorphicFormsFiniteGL → ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (π : CuspSub E a), ∀ᶠ w : HeightOneSpectrum (𝓞 E) in Filter.cofinite, ∃ B, GlobalTheory.LFun.HasSatGL w (π.locRep w) B := by
  first | exact @GlobalTheory.CuspRep.UnrSat.eventually_hasSatGL_locRep | exact GlobalTheory.CuspRep.UnrSat.eventually_hasSatGL_locRep | (intros; apply GlobalTheory.CuspRep.UnrSat.eventually_hasSatGL_locRep <;> assumption)
