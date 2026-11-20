import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ThetaSystemSumCharacterOrthogonalEqZero
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical
open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR GlobalTheory.UT
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.TestFibre
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaSystem_sum_character_orthogonal_eq_zero : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (F : Type) [Field F] (ζ : F), IsPrimitiveRoot ζ ((S.r * S.N) ^ 2) → ∀ (H : AddSubgroup S.Gam) [Fintype (S.perp H)] (a : S.Gam), a ∉ H → ∑ t : S.perp H, ζ ^ (S.r * S.N * (eStd S.g _ (t : S.Gam) a).val) = 0 := by
  first | exact @GlobalTheory.thetaSys_sum_perp_char_eq_zero | exact GlobalTheory.thetaSys_sum_perp_char_eq_zero | (intros; apply GlobalTheory.thetaSys_sum_perp_char_eq_zero <;> assumption)
