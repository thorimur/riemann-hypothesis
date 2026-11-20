import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ProductSupportInSubgroupTheta
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.product_support_in_subgroup_theta : (AllPre fun {V} _ _ _ {D} {A} {G} _ _ U => ∀ (Λ : AddSubgroup D.X) (k l : ℕ) (σ : U.SecGT (𝟙_ _) k) (σ' : U.SecGT (𝟙_ _) l) (σ'' : U.SecGT (𝟙_ _) (k + l)) f f' f'', U.ExpT (𝟙_ _) k σ f → U.ExpT (𝟙_ _) l σ' f' → U.ExpT (𝟙_ _) (k + l) σ'' f'' → (∀ (Z : Scheme.{0}) (r : Z ⟶ (𝟙_ _ ⊗ G).left) (z : Z) (J), Good U.P.L.L z J → sval σ'' r z J = sval σ r z J * sval σ' r z J) → (∀ α ∉ Λ, ∀ j, (f α).f j = 0) → (∀ α ∉ Λ, ∀ j, (f' α).f j = 0) → ∀ α ∉ Λ, ∀ j, (f'' α).f j = 0) := by
  first | exact @GlobalTheory.MulSupp.main | exact GlobalTheory.MulSupp.main | (intros; apply GlobalTheory.MulSupp.main <;> assumption)
