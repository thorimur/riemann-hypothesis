import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.DescendedBundleAmpleSpecialFibre
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.UU
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.descended_bundle_ample_special_fibre : (∀ (k : Type) [Field k] [IsAlgClosed k] (B : Over (Sp k)) [GrpObj B] (g n : ℕ), IsAbelianScheme B → SmoothOfRelativeDimension g B.hom → (n : k) ≠ 0 → Nat.card {x : (𝟙_ (Over (Sp k)) ⟶ B) // x ^ n = 1} = n ^ (2 * g)) → Laws → AllSet fun s => ∀ t : Tower s, RelAmple (t.l 0).Q.B (t.l 0).D.M.L.L := by
  first | exact @GlobalTheory.UU.AmpleZero.relAmple_zero | exact GlobalTheory.UU.AmpleZero.relAmple_zero | (intros; apply GlobalTheory.UU.AmpleZero.relAmple_zero <;> assumption)
