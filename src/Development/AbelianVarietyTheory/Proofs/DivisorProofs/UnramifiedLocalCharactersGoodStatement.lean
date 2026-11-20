import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnramifiedLocalCharactersGood
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.ThK.SquareIntegrability GlobalTheory.ThK.DetProd
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unramified_local_characters_good : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (B : Base F E) (a a' : ℕ) (G : Geo σ a a') (X : Chars F E)
    (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ w : HeightOneSpectrum (𝓞 E), X.Good (w.under (𝓞 F)) →
      GlobalTheory.ThK.DetProd.IsUnramAt w (GlobalTheory.LFun.locChar X.α w) ∧ GlobalTheory.ThK.DetProd.IsUnramAt w (GlobalTheory.LFun.locChar X.β w) := by
  first | exact @GlobalTheory.GoodPlaceUnr.unram_of_good | exact GlobalTheory.GoodPlaceUnr.unram_of_good | (intros; apply GlobalTheory.GoodPlaceUnr.unram_of_good <;> assumption)
