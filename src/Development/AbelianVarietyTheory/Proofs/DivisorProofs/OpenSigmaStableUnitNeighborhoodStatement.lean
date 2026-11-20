import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OpenSigmaStableUnitNeighborhood
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.open_sigma_stable_unit_neighborhood : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (m : ℕ), 0 < m → ∃ U : Subgroup (AdeleRing (𝓞 F) F ⊗[F] E)ˣ, IsOpen (U : Set (AdeleRing (𝓞 F) F ⊗[F] E)ˣ) ∧
      (∀ x ∈ U, Units.map (Algebra.TensorProduct.map (AlgHom.id (AdeleRing (𝓞 F) F) (AdeleRing (𝓞 F) F)) σ).toRingHom.toMonoidHom x ∈ U) ∧
      ∀ x ∈ U, ∃ s ∈ HeckeCharacterZeroLocus.ThmBIn.intAE F E,
        HeckeCharacterZeroLocus.ThmBIn.finPart F E (x : AdeleRing (𝓞 F) F ⊗[F] E) = 1 + (m : FiniteAdeleRing (𝓞 F) F ⊗[F] E) * s := by
  first | exact @GlobalTheory.IdeleCongr.exists_open_congruence_subgroup | exact GlobalTheory.IdeleCongr.exists_open_congruence_subgroup | (intros; apply GlobalTheory.IdeleCongr.exists_open_congruence_subgroup <;> assumption)
