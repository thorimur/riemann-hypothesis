import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsAdditiveOfUniversal
import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.EvalFrameOrd
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual CompanionTheory.ObstructionTrivialLocus
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CompanionTheory.PointSurjectivity

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CompanionTheory.PicField

theorem pic_eq_zero (k : Type) [Field k] (c : Pic (Sp k)) : c = 0 := by
  obtain ⟨p⟩ : Nonempty (Sp k) := inferInstance
  obtain ⟨V, hV, hc⟩ := exists_pull_eq_zero c p
  have hV' : V = ⊤ := by
    have hs : Subsingleton (Sp k) := by
      unfold Sp; infer_instance
    ext x
    simp only [TopologicalSpace.Opens.coe_top, Set.mem_univ, iff_true]
    exact (Subsingleton.elim x p) ▸ hV
  subst hV'
  have : IsIso (⊤ : (Sp k).Opens).ι := (Sp k).topIso.isIso_hom
  have e : c = CechPic.pull (inv (⊤ : (Sp k).Opens).ι) (CechPic.pull (⊤ : (Sp k).Opens).ι c) := by
    rw [← pull_comp, IsIso.inv_hom_id, pull_id]
  rw [e, hc, map_zero]

end GlobalTheory.CompanionTheory.PicField
