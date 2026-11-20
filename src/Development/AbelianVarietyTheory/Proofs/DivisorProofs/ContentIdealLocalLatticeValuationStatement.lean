import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContentIdealLocalLatticeValuation
open scoped TensorProduct NNReal Matrix
open NumberField MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.EisRes
open GlobalTheory.Doubling (absE)
open IsDedekindDomain
open scoped nonZeroDivisors

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.content_ideal_local_lattice_valuation : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (n : ℕ)
    (L : Submodule (𝓞 E) (Fin n → E)), Submodule.IsLattice E L → ∀ u : Fin n → E, u ≠ 0 →
    ∀ I : FractionalIdeal (𝓞 E)⁰ E, I ≠ 0 → (∀ c : E, c ∈ I ↔ c • u ∈ L) →
    ∀ (v : HeightOneSpectrum (𝓞 F)) (c : Fv F v ⊗[F] E),
      (c • fun i => (1 : Fv F v) ⊗ₜ[F] u i) ∈ latLoc F L v →
      ∀ w : HeightOneSpectrum (𝓞 E), w.under (𝓞 F) = v →
          GlobalTheory.UnrTate.valAt v w c ≤ WithZero.exp (-FractionalIdeal.count E w I) := by
  first | exact @GlobalTheory.LineLocVal.valAt_le_of_smul_mem_latLoc | exact GlobalTheory.LineLocVal.valAt_le_of_smul_mem_latLoc | (intros; apply GlobalTheory.LineLocVal.valAt_le_of_smul_mem_latLoc <;> assumption)
