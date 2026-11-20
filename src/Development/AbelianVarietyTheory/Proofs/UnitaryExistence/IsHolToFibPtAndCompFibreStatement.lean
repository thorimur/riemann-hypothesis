import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IsHolToFibPtAndCompFibre
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
theorem _root_.GlobalTheory.T.isHolTo_fibPt_and_comp_fibre : ∀ (X : Scheme.{0}) (G : Over X) (y : Sp ℂ ⟶ X) (g : ℕ) (e : (Fin g → ℂ) → (Over.mk y ⟶ G)), IsHolTo Set.univ (fun z => (e z).left) → IsHolTo Set.univ (fun z => fibPt G (e z)) ∧ ∀ (Y : Scheme.{0}) (ψ : pullback G.hom y ⟶ Y), IsHolTo Set.univ (fun z => fibPt G (e z) ≫ ψ) := by
  first | exact @GlobalTheory.HolFibre.isHolTo_fibPt_and_comp | exact GlobalTheory.HolFibre.isHolTo_fibPt_and_comp | (intros; apply GlobalTheory.HolFibre.isHolTo_fibPt_and_comp <;> assumption)
