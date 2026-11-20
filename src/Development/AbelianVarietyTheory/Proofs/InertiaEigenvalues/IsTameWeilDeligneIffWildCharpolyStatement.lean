import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsTameWeilDeligneIffWildCharpoly
open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Published
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isTameWeilDeligne_iff_wild_charpoly : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w) (y : WD h), IsTameWD y ↔ ∀ σ : Weil h, Formalism.MainNotions.BlochKatoReduction.IsWild A (σ : G E Ω) → y.charPol σ = (X - 1) ^ y.lpDim := by
  first | exact @GlobalTheory.LlcTame.isTameWD_iff_charPol | exact GlobalTheory.LlcTame.isTameWD_iff_charPol | (intros; apply GlobalTheory.LlcTame.isTameWD_iff_charPol <;> assumption)
