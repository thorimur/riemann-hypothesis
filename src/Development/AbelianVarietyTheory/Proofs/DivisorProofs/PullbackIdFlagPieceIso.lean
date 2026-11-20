import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.EvalFrameOrd
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.CategoryTheory.EffectiveEpi.Comp
import Mathlib.CategoryTheory.ExtremalEpi
import Mathlib.CategoryTheory.Limits.Shapes.Countable
import Mathlib.CategoryTheory.Monoidal.Mon
import Mathlib.Combinatorics.Quiver.ReflQuiver
open NumberField MvPolynomial Filter Topology Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Published
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt
open scoped Classical
open Formalism.BasicNotions.DV Formalism.MainNotions.WeightThresholdDefs GlobalTheory.FlagAr GlobalTheory.ShFam.Pad GlobalTheory.VB

namespace GlobalTheory

theorem pullback_id_lift_step_self : ∀ {B Y : Scheme.{0}} (π : Y ⟶ B) (E : B.Modules) (F : Y.Modules)
    (ι : F ⟶ (Scheme.Modules.pullback π).obj E) (w : 𝟙 Y ≫ π = π),
    ∃ e : (Scheme.Modules.pullback (𝟙 Y)).obj F ≅ F, e.hom ≫ ι =
      (Scheme.Modules.pullback (𝟙 Y)).map ι ≫ (Scheme.Modules.pullbackComp (𝟙 Y) π).hom.app E ≫
        (Scheme.Modules.pullbackCongr w).hom.app E := by
  intro B Y π E F ι w
  refine ⟨(Scheme.Modules.pullbackId Y).app F, ?_⟩
  have h1 := congrArg (fun t => NatTrans.app t E)
    (Scheme.Modules.pseudofunctor_right_unitality π)
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.rightUnitor_hom_app,
    eqToHom_app] at h1
  erw [Category.comp_id] at h1
  have h2 : (Scheme.Modules.pullbackComp (𝟙 Y) π).hom.app E ≫
      (Scheme.Modules.pullbackCongr w).hom.app E =
      (Scheme.Modules.pullbackId Y).hom.app ((Scheme.Modules.pullback π).obj E) := by
    rw [← cancel_epi ((Scheme.Modules.pullbackComp (𝟙 Y) π).inv.app E), h1,
      Iso.inv_hom_id_app_assoc]
    simp [Scheme.Modules.pullbackCongr, eqToHom_app]
  have h3 := (Scheme.Modules.pullbackId Y).hom.naturality ι
  simp only [Functor.id_map] at h3
  rw [h2, h3]
  rfl

end GlobalTheory
