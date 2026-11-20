import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsTameOfMemWeilDeligneListSum

open NumberField IsDedekindDomain ValuativeRel Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isTame_of_mem_weilDeligneListSum : ∀ {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}
    (l : List (WD h)), IsTameWD (sumList l) → ∀ y ∈ l, IsTameWD y := by
  first | (exact @GlobalTheory.TameSum.isTameWD_of_mem_sumList) | (exact GlobalTheory.TameSum.isTameWD_of_mem_sumList) | (intros; apply GlobalTheory.TameSum.isTameWD_of_mem_sumList  <;> assumption)
