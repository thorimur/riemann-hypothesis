import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechPicardPullbackZpowEqMumfordFormula
open CategoryTheory MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AmpleGen
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cechPicardPullback_zpow_eq_mumford_formula : ∀ (K : Type) [Field K] (A : Over (Sp K)) [GrpObj A], IsAbelianScheme A → ∀ (L : LB A.left) (hL : L.IsLB) (T : Over (Sp K)) (z : T ⟶ A) (n : ℤ), GlobalTheory.CechPic.pull (z ^ n).left (GlobalTheory.CechPic.cls L hL) = tri n • GlobalTheory.CechPic.pull z.left (GlobalTheory.CechPic.cls L hL) + tri (-n) • GlobalTheory.CechPic.pull (z⁻¹).left (GlobalTheory.CechPic.cls L hL) := by
  first | exact @GlobalTheory.PowPull.pull_zpow | exact GlobalTheory.PowPull.pull_zpow | (intros; apply GlobalTheory.PowPull.pull_zpow <;> assumption)
