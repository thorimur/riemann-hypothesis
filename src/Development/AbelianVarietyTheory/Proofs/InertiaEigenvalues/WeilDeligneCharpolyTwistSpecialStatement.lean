import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WeilDeligneCharpolyTwistSpecial
open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Published
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weilDeligne_charpoly_twist_special : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w) (x : WD h), (x.lpTw 0).lpChar (WD.lpSp h 1) = x ∧ ∀ (l : ℕ) (σ : Weil h), ((x.lpTw (((l : ℝ) - 1) / 2)).lpChar (WD.lpSp h l)).charPol σ = ((Multiset.range l).map fun j : ℕ => (x.lpTw j).charPol σ).prod := by
  first | exact @GlobalTheory.WeilDeligne.charPol_lpTw_lpChar_lpSp | exact GlobalTheory.WeilDeligne.charPol_lpTw_lpChar_lpSp | (intros; apply GlobalTheory.WeilDeligne.charPol_lpTw_lpChar_lpSp <;> assumption)
