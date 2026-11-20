import Development.AutomorphicSpectrum.Proofs.GeometryProofs.FiniteMapEqOfThickeningsEq
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open GlobalTheory.CompanionTheory.Ar.BT ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_map_eq_of_thickenings_eq : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (I : Ideal R) [IsAdicComplete I R] (X Y : Over (Spec (CommRingCat.of R))) [IsFinite X.hom] [IsFinite Y.hom] (f g : X ⟶ Y), (∀ e, (Over.pullback (thick R I e)).map f = (Over.pullback (thick R I e)).map g) → f = g := by
  first | exact @GlobalTheory.CompanionTheory.Ar.BT.EqRed.eq_of_reductions | exact GlobalTheory.CompanionTheory.Ar.BT.EqRed.eq_of_reductions | (intros; apply GlobalTheory.CompanionTheory.Ar.BT.EqRed.eq_of_reductions <;> assumption)
