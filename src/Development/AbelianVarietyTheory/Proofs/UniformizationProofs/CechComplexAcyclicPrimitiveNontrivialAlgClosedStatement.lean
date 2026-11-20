import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.CechComplexAcyclicPrimitiveNontrivialAlgClosed
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.UU
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cechComplex_acyclic_primitive_nontrivial_algClosed : ∀ (K : Type) [Field K] [IsAlgClosed K] (B : Over (Spec (CommRingCat.of K))) [GrpObj B] [IsCommMonObj B], IsAbelianScheme B → IsProjBy B.hom → ∀ M : LB B.left, M.IsLB → (∃ u : LB.Gen (abelian₂ B M), u.IsGen) → ¬ Triv M → (∀ (κ : Type) [LinearOrder κ] [Fintype κ] (D : κ → (B.left).Opens), (∀ i, IsAffineOpen (D i)) → ⨆ i, D i = ⊤ → (cechLB (B.hom) (M) D).Acyclic) := by
  first | exact @GlobalTheory.PrimVan.acyclic_cechLB_of_primitive | exact GlobalTheory.PrimVan.acyclic_cechLB_of_primitive | (intros; apply GlobalTheory.PrimVan.acyclic_cechLB_of_primitive <;> assumption)
