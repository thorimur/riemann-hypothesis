import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AbsNormPlaceLeOfFrobenius
open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Published
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.absNorm_place_le_of_frobenius : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)), IsPlaceOver A w → ∀ q : ℕ, 1 < q → ∀ σ : G E Ω, IsFrob A q σ → normV w ≤ q := by
  first | exact @GlobalTheory.NormLeFrob.normV_le_of_isFrob | exact GlobalTheory.NormLeFrob.normV_le_of_isFrob | (intros; apply GlobalTheory.NormLeFrob.normV_le_of_isFrob <;> assumption)
