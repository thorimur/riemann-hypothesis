import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSymplecticLevelPrincipalSiegelAlgClosed
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.SiegTh Classical
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.SiegLev GlobalTheory.SiegLevCalc GlobalTheory.SiegelPullComp GlobalTheory.SiegelPull
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_symplecticLevel_principalSiegel_algClosed : ∀ (g n N : ℕ) (B : Type) [CommRing B] (ζ : B) (K : Type) [Field K] [IsAlgClosed K] (s : Sp K ⟶ Sp B) (c : SiegPre g n ζ s) (b : TBase K N), Odd N → 3 ≤ N → c.Principal → SmoothOfRelativeDimension g c.A.hom → ∃ C : SiegPre g N (b.ζ : K) (𝟙 (Sp K)), SRel C c 0 0 (𝟙 _) := by
  first | exact @GlobalTheory.SiegLift.exists_level_of_forget | exact GlobalTheory.SiegLift.exists_level_of_forget | (intros; apply GlobalTheory.SiegLift.exists_level_of_forget <;> assumption)
