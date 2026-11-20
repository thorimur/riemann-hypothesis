import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.NonemptyFormalUniformisationTower
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
open GlobalTheory.LN
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.nonempty_formalUniformisationTower : Laws → Laws2 → ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (I : Ideal R), admitted R I → ∀ (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] (P : CP G), IsSemiAbelian G → HypW G P.L.L → IsProper (pullback.snd G.hom (jK R)) → SplitOver G I → ∃ (X : Type) (_ : AddCommGroup X) (_ : Module.Free ℤ X) (_ : Module.Finite ℤ X), Nonempty (TowerR I P X) := by
  first | exact @GlobalTheory.FormalTower.nonempty_towerR | exact GlobalTheory.FormalTower.nonempty_towerR | (intros; apply GlobalTheory.FormalTower.nonempty_towerR <;> assumption)
