import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TameWeilDeligneUnderIdentityRelation

open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Published
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.place_iso_compatible_local_langlands_one : ∀ (E E' Ω : Type) [Field E] [NumberField E] [Field E'] [NumberField E'] [Field Ω] [Algebra E Ω] [Algebra E' Ω] [IsAlgClosure E Ω] [IsAlgClosure E' Ω] (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (w' : HeightOneSpectrum (𝓞 E')) (h : IsPlaceOver A w) (h' : IsPlaceOver A w') (j : E →+* E') (i : w.adicCompletion E ≃+* w'.adicCompletion E'), GlobalTheory.LocLanglands.PlaceIso A w A w' (RingEquiv.refl Ω) j i → ∀ (y : WD h) (y' : WD h'), WDRel (RingEquiv.refl Ω) y y' → IsTameWD y → IsTameWD y' := by
  first | (exact @GlobalTheory.LocLanglands.isTameWD_of_wdRel_refl) | (exact GlobalTheory.LocLanglands.isTameWD_of_wdRel_refl) | (intros; apply GlobalTheory.LocLanglands.isTameWD_of_wdRel_refl  <;> assumption)
