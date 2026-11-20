import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinitelyGeneratedLatticeFullEmbedding
import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.EvalFrameOrd
open NumberField MeasureTheory ReciprocityTheory.GeometryOfNumbersTheory ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.LieHt
open scoped ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finitely_generated_lattice_full_embedding : ∀ (K : Type) [Field K] [NumberField K] (m : ℕ) (W : Submodule (𝓞 K) (Fin m → K)), W.FG → ∃ α : (Fin (latRank K W) → K) →ₗ[K] (Fin m → K), Function.Injective α ∧ Full (W.comap (α.restrictScalars (𝓞 K))) ∧ (W.comap (α.restrictScalars (𝓞 K))).map (α.restrictScalars (𝓞 K)) = W := by
  first | exact @GlobalTheory.exists_injective_full_comap_map_eq | exact GlobalTheory.exists_injective_full_comap_map_eq | (intros; apply GlobalTheory.exists_injective_full_comap_map_eq <;> assumption)
