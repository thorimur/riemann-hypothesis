import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsProperInfIdealSheafImage
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.AbLaw GlobalTheory.FormalAlg
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isProper_inf_ideal_sheaf_image : ∀ (S W W' : Scheme.{0}) (f : W ⟶ S) (π : W' ⟶ W), IsSeparated f → LocallyOfFiniteType f → ∀ (T' : W'.IdealSheafData) (T'' : W.IdealSheafData), IsProper (T'.subschemeι ≫ π ≫ f) → IsProper (T''.subschemeι ≫ f) → IsProper ((T'.map π ⊓ T'').subschemeι ≫ f) := by
  first | exact @GlobalTheory.isProper_map_inf_subschemeι | exact GlobalTheory.isProper_map_inf_subschemeι | (intros; apply GlobalTheory.isProper_map_inf_subschemeι <;> assumption)
