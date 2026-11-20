import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ValuationEqOneOfCongruentGlobalApprox
open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Published
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.valuation_eq_one_of_congruent_global_approx : ∀ (E : Type) [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) (x : w.adicCompletion E),
    x ≠ 0 → Valued.v x ≤ 1 → (∀ a : ℕ, 0 < a → ∀ t : w.adicCompletion E, t ≠ 0 → ∃ k : Eˣ,
      (∀ v : HeightOneSpectrum (𝓞 E), v ≠ w →
        v.valuation E (((k : E) - 1) / (a : E)) ≤ 1 ∧ v.valuation E ((k : E)⁻¹) ≤ 1) ∧
      Valued.v (algebraMap E (w.adicCompletion E) (k : E) - x) ≤ Valued.v t) → Valued.v x = 1 := by
  first | exact @GlobalTheory.OrdZeroUnit.valuation_eq_one_of_approx | exact GlobalTheory.OrdZeroUnit.valuation_eq_one_of_approx | (intros; apply GlobalTheory.OrdZeroUnit.valuation_eq_one_of_approx <;> assumption)
