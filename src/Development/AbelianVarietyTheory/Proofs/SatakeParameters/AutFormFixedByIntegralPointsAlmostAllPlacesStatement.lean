import Development.AbelianVarietyTheory.Proofs.SatakeParameters.AutFormFixedByIntegralPointsAlmostAllPlaces
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.Published GlobalTheory.AboveL
open GlobalTheory.Cong.AdaptLev
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.autForm_fixed_by_integralPoints_almostAllPlaces : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (a : ℕ) (φ : UA E a → ℂ), IsAutFormU φ → ∀ᶠ w in Filter.cofinite, ∀ x ∈ GlobalTheory.Cong.AdaptLev.intU a w, RU E a x φ = φ := by
  first | (exact @GlobalTheory.Cong.AutFormFix.fixed_intU_eventually) | (exact GlobalTheory.Cong.AutFormFix.fixed_intU_eventually) | (intros; apply GlobalTheory.Cong.AutFormFix.fixed_intU_eventually  <;> assumption)
