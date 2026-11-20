import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsPreimagePositiveResidueDegree
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.CechPic
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_preimage_positive_residue_degree : ∀ (W Z : Scheme.{0}) (g : W ⟶ Z) [QuasiCompact g] [LocallyOfFiniteType g] (z : Z), z ∈ Set.range g → ∃ w, g w = z ∧ 0 < g.residueDegree w := by
  first | exact @GlobalTheory.exists_residueDegree_pos_of_mem_range | exact GlobalTheory.exists_residueDegree_pos_of_mem_range | (intros; apply GlobalTheory.exists_residueDegree_pos_of_mem_range <;> assumption)
