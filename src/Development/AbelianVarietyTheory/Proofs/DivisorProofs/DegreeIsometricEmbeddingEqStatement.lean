import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DegreeIsometricEmbeddingEq
open NumberField MeasureTheory ReciprocityTheory.GeometryOfNumbersTheory ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.LieHt
open scoped ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.degree_isometric_embedding_eq : ∀ (K : Type) [Field K] [NumberField K] (n m : ℕ) (hW : HermFam K (Fin n → K)) (h : HermFam K (Fin m → K)) (α : (Fin n → K) →ₗ[K] (Fin m → K)), Function.Injective α → (∀ σ y z, hW.form σ y z = h.form σ (α y) (α z)) → ∀ E : Submodule (𝓞 K) (Fin n → K), E.FG → deg hW E = deg h (E.map (α.restrictScalars (𝓞 K))) := by
  first | exact @GlobalTheory.deg_map_of_isometry | exact GlobalTheory.deg_map_of_isometry | (intros; apply GlobalTheory.deg_map_of_isometry <;> assumption)
