import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ThickeningGroupHomExtends
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open GlobalTheory.CompanionTheory.Ar.BT ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thickening_group_hom_extends : ∀ (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] (I : Ideal R) [IsAdicComplete I R] (P Q P' Q' : Over (Spec (CommRingCat.of R))) [GrpObj P] [GrpObj Q] [GrpObj P'] [GrpObj Q'] [IsFinite P.hom] [IsFinite Q.hom] (jP : P ⟶ P') (jQ : Q ⟶ Q') [IsMonHom jP] [IsMonHom jQ] [Mono jQ] (φ : ∀ e, thickObj R I e P' ⟶ thickObj R I e Q'), (∀ e, IsMonHom (φ e)) → (∀ e, thickMap R I e P' ≫ (φ (e + 1)).left = (φ e).left ≫ thickMap R I e Q') → (∀ e, ∃ w : thickObj R I e P ⟶ thickObj R I e Q, w ≫ (Over.pullback (thick R I e)).map jQ = (Over.pullback (thick R I e)).map jP ≫ φ e) → ∃ c : P ⟶ Q, IsMonHom c ∧ ∀ e, (Over.pullback (thick R I e)).map (c ≫ jQ) = (Over.pullback (thick R I e)).map jP ≫ φ e := by
  first | exact @GlobalTheory.CompanionTheory.Ar.BT.LiftHom.lift_hom | exact GlobalTheory.CompanionTheory.Ar.BT.LiftHom.lift_hom | (intros; apply GlobalTheory.CompanionTheory.Ar.BT.LiftHom.lift_hom <;> assumption)
