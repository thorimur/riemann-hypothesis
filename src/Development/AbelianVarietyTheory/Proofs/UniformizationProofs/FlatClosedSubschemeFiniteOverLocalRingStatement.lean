import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.FlatClosedSubschemeFiniteOverLocalRing
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.UU
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flat_closedSubscheme_finite_over_localRing : ∀ (V : Type) [CommRing V] [IsLocalRing V] (X H : Scheme.{0}) (f : X ⟶ Spec (CommRingCat.of V)) (j : H ⟶ X), IsClosedImmersion j → IsFinite (j ≫ f) → (∀ (h : H) (σ : V →+* X.presheaf.stalk (j h)), X.fromSpecStalk (j h) ≫ f = Spec.map (CommRingCat.ofHom σ) → IsLocalHom σ → ∃ I : Ideal (X.presheaf.stalk (j h)), ((Ideal.Quotient.mk I).comp σ).Flat ∧ ∀ (R : Type) [CommRing R] [IsLocalRing R] (φ : X.presheaf.stalk (j h) →+* R), (∃ y : Spec (CommRingCat.of R) ⟶ H, y ≫ j = Spec.map (CommRingCat.ofHom φ) ≫ X.fromSpecStalk (j h)) ↔ I ≤ RingHom.ker φ) → Flat (j ≫ f) := by
  first | exact @GlobalTheory.StabFlat.flat_of_isFinite_of_ideals | exact GlobalTheory.StabFlat.flat_of_isFinite_of_ideals | (intros; apply GlobalTheory.StabFlat.flat_of_isFinite_of_ideals <;> assumption)
