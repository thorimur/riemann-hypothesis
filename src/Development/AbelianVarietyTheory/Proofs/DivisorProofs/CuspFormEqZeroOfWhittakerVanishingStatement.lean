import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CuspFormEqZeroOfWhittakerVanishing
open NumberField IsDedekindDomain GlobalTheory.CuspRep Formalism.UG GlobalTheory.LFun Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cusp_form_eq_zero_of_whittaker_vanishing : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (φ : Sm E a), IsCuspForm φ → (∀ g, GlobalTheory.JSW.whit φ.1 g = 0) → φ = 0 := by
  first | exact @GlobalTheory.JSW.eq_zero_of_whit_eq_zero | exact GlobalTheory.JSW.eq_zero_of_whit_eq_zero | (intros; apply GlobalTheory.JSW.eq_zero_of_whit_eq_zero <;> assumption)
