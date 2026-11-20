import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.EvalFrameOrd
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsGrpPullback
open CategoryTheory AlgebraicGeometry NumberField MonObj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.Geo GlobalTheory.LocM GlobalTheory.ShFam GlobalTheory.ShFam.Pad
open Formalism.MainNotions.DIV.Cons (intO SCF)
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.WeilTorsChar

theorem exists_mulEquiv_points {S S' : Scheme.{0}} (f : S' ⟶ S) (G : Over S) (G' : Over S') [GrpObj G] [GrpObj G']
    (φ : G'.left ⟶ G.left) (h : IsGrpPullback G' G f φ) (T : Over S') :
    ∃ Φ : (T ⟶ G') ≃* (Over.mk (T.hom ≫ f) ⟶ G), ∀ x, (Φ x).left = x.left ≫ φ := by
  let F : (T ⟶ G') → (Over.mk (T.hom ≫ f) ⟶ G) := fun x =>
    Over.homMk (x.left ≫ φ) (by
      change (x.left ≫ φ) ≫ G.hom = T.hom ≫ f
      rw [Category.assoc, h.1.w, ← Category.assoc, Over.w x])
  let I : (Over.mk (T.hom ≫ f) ⟶ G) → (T ⟶ G') := fun y =>
    Over.homMk (h.1.lift y.left T.hom (Over.w y)) (h.1.lift_snd _ _ _)
  refine ⟨⟨⟨F, I, fun x => ?_, fun y => ?_⟩, fun x y => ?_⟩, fun _ => rfl⟩
  · apply Over.OverMorphism.ext
    apply h.1.hom_ext
    · exact h.1.lift_fst _ _ _
    · exact (h.1.lift_snd _ _ _).trans (Over.w x).symm
  · apply Over.OverMorphism.ext
    exact h.1.lift_fst _ _ _
  · apply Over.OverMorphism.ext
    exact (h.2 T x y (F x) (F y) rfl rfl).symm

end GlobalTheory.WeilTorsChar
