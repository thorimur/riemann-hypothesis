import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIdeleWithArchimedeanComponents
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.DescB
open GlobalTheory.Doubling (absE)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_idele_with_archimedean_components : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (τ : ∀ w : InfinitePlace F, EmbOver E w) (β : InfinitePlace F → ℂ), IsCMExt F E σ → (∀ w, β w ≠ 0) → ∃ t : (AE F E)ˣ, At (evI F) (t.1 - 1) ∧ ∀ w, piInf (τ w) t.1 = β w := by
  first | exact @GlobalTheory.ThK.exists_unit_at_evI_piInf_eq | exact GlobalTheory.ThK.exists_unit_at_evI_piInf_eq | (intros; apply GlobalTheory.ThK.exists_unit_at_evI_piInf_eq <;> assumption)
