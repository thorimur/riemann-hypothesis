import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.KTrivOfKTrivNonemptyOpenNormalCharZero
import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.EvalFrameOrd
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM GlobalTheory.SiegLev GlobalTheory.SiegelTor
open scoped CategoryTheory.Obj
open GlobalTheory.IndefiniteRowSideFullHecke.SiegelFamilyZetaUnit GlobalTheory.SiegelTypings
open GlobalTheory.PrincSubring

attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.KTrivFlatDescent

theorem trivAlong_of_flat_surjective : ∀ {S S' S'' : Scheme.{0}} (G : Over S) [GrpObj G] (L : LB G.left) (g : S' ⟶ S) (f : S'' ⟶ S') [Flat f] [Surjective f], L.IsLB → GlobalTheory.KTrivSpread.TrivAlong G L (f ≫ g) → GlobalTheory.KTrivSpread.TrivAlong G L g := by
  intro S S' S'' G _ L g f _ _ _ h T a ha x hx
  let u := pullback.fst a f
  have hu : Epi u := Flat.epi_of_flat_of_surjective _
  let T' : Over S := Over.mk (u ≫ T.hom)
  let U : T' ⟶ T := Over.homMk u rfl
  have hs : pullback.snd a f ≫ f ≫ g = T'.hom := by
    show pullback.snd a f ≫ f ≫ g = u ≫ T.hom
    rw [← Category.assoc, ← pullback.condition, Category.assoc, ha]
  have e₁ : U ≫ x = 1 := h T' (pullback.snd a f) hs (U ≫ x) (hx.comp U)
  have e₂ : U ≫ x = U ≫ (1 : T ⟶ G) := by rw [e₁, MonObj.comp_one]
  exact Over.OverMorphism.ext ((cancel_epi u).1 (congrArg (fun q => q.left) e₂))

end GlobalTheory.KTrivFlatDescent
