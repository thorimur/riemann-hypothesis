import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.PicardMayerVietorisExtend

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj CategoryTheory.MonObj
open GlobalTheory.CechPic GlobalTheory.AbDual
open GlobalTheory.IndefiniteRowSideFullHecke.ZeroSectionBase (IsPrincipalPol sqToBase)
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.picard_mayer_vietoris_extend : ∀ (X : Scheme.{0}) (W V : X.Opens) (p : Pic W.toScheme),
    pull (X.homOfLE (inf_le_left : W ⊓ V ≤ W)) p = 0 →
    ∃ q : Pic (W ⊔ V).toScheme, pull (X.homOfLE (le_sup_left : W ≤ W ⊔ V)) q = p := by
  first | exact @GlobalTheory.CompanionTheory.CechMV.exists_extend_of_pull_inf_eq_zero | exact GlobalTheory.CompanionTheory.CechMV.exists_extend_of_pull_inf_eq_zero | (intros; apply GlobalTheory.CompanionTheory.CechMV.exists_extend_of_pull_inf_eq_zero <;> assumption)
