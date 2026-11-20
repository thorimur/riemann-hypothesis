import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.RelAmpleOfSamePolarization

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj CategoryTheory.MonObj
open GlobalTheory.CechPic GlobalTheory.AbDual
open GlobalTheory.IndefiniteRowSideFullHecke.ZeroSectionBase (IsPrincipalPol sqToBase)
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rel_ample_of_same_polarization : ∀ (K : Type) [Field K] [IsAlgClosed K] (B : Over (Sp K)) [GrpObj B], IsAbelianScheme B →
    ∀ (M L : LB B.left) (hM : M.IsLB) (hL : L.IsLB), Out.RelAmple B L → Out.KTriv B L →
    lam (cls M hM) (fst B B) (snd B B) = lam (cls L hL) (fst B B) (snd B B) → Out.RelAmple B M := by
  first | exact @GlobalTheory.CompanionTheory.AmpleForm.relAmple_of_lam_eq | exact GlobalTheory.CompanionTheory.AmpleForm.relAmple_of_lam_eq | (intros; apply GlobalTheory.CompanionTheory.AmpleForm.relAmple_of_lam_eq <;> assumption)
