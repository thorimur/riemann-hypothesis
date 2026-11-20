import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RealMultIsogenyFiniteEtale

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.RealMult
open GlobalTheory.AbLaw GlobalTheory.CechPic
attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.real_mult_isogeny_finite_etale : ∀ {F : Type} [Field F] [NumberField F] {𝔠 : FracId F} {Ω : Type} [Field Ω] [IsAlgClosed Ω] (X : Obj F 𝔠 (Sp Ω)) (b : 𝓞 F), ((Algebra.norm ℤ b : ℤ) : Ω) ≠ 0 → IsFinite (X.rm.act b).left ∧ Etale (X.rm.act b).left ∧ Finite {y : 𝟙_ (Over (Sp Ω)) ⟶ X.A // y ≫ X.rm.act b = 1} := by
  first | exact @GlobalTheory.OActFinEtNorm.finite_etale_act_of_norm | exact GlobalTheory.OActFinEtNorm.finite_etale_act_of_norm | (intros; apply GlobalTheory.OActFinEtNorm.finite_etale_act_of_norm <;> assumption)
