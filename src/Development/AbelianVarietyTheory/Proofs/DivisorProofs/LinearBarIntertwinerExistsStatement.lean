import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LinearBarIntertwinerExists
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SmGL GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.LeviBlockExponent GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
  GlobalTheory.UAut GlobalTheory.SiegelSet GlobalTheory.ThK.SquareIntegrability GlobalTheory.CuspBlock GlobalTheory.LFun.SplitTie
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.linear_bar_intertwiner_exists : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E) (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W),
    IsTriple B G X om om' → ∀ ι, G.M'.IsLinBar B.ψ B.τ₁ 1 1 ι →
    ∃ (S : GL (Fin (a + a')) (Fv F B.v₁) → ((Fin a' × Fin (a + a') → Fv F B.v₁) → ℂ) → (Fin a' × Fin (a + a') → Fv F B.v₁) → ℂ)
      (χ : (Fv F B.v₁)ˣ →* ℂˣ),
      (∀ g, ∃ h ∈ UAt σ G.W (evFin F B.v₁), ∀ φ ∈ GlobalTheory.WeilM.SB (Fin a' × Fin (a + a') → Fv F B.v₁),
        S g φ ∈ GlobalTheory.WeilM.SB (Fin a' × Fin (a + a') → Fv F B.v₁) ∧ Acts (evFin F B.v₁) (om' (1, h)) φ (S g φ)) ∧
      (∀ g, ∀ φ ∈ GlobalTheory.WeilM.SB (Fin a' × Fin (a + a') → Fv F B.v₁),
        ι (S g φ) = fun Y => (χ (Matrix.GeneralLinearGroup.det g) : ℂ) * ι φ (Y * g.val)) ∧
      ∀ h ∈ UAt σ G.W (evFin F B.v₁), ∀ c : ℂ,
        (∀ φ ∈ GlobalTheory.WeilM.SB (Fin a' × Fin (a + a') → Fv F B.v₁), ∀ φ₁ ∈ GlobalTheory.WeilM.SB (Fin a' × Fin (a + a') → Fv F B.v₁),
          Acts (evFin F B.v₁) (om' (1, h)) φ φ₁ → ι φ₁ = c • fun Y => ι φ (Y * (mat h).map (piW B.τ₁))) →
        c = (χ (Matrix.GeneralLinearGroup.det (GlobalTheory.LocalUnitSubgroupClosure.cmpGL B.τ₁ h)) : ℂ) := by
  first | exact @GlobalTheory.WFamilyBar.family | exact GlobalTheory.WFamilyBar.family | (intros; apply GlobalTheory.WFamilyBar.family <;> assumption)
