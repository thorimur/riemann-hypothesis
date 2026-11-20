import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompactOpenSchwartzFiniteDecomposition

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

open scoped Classical

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.compact_open_schwartz_finite_decomposition : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ], ∀ Φ ∈ schA F κ,
    ∃ W ∈ 𝓝 (0 : κ → Af F), ∀ U : AddSubgroup (κ → Af F), IsOpen (U : Set (κ → Af F)) → IsCompact (U : Set (κ → Af F)) →
      (U : Set (κ → Af F)) ⊆ W →
      ∃ (T : Finset ((κ → Af F) ⧸ U)) (G : (κ → Af F) ⧸ U → SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ),
        (∀ (c : κ → Af F) (X : κ → mixedEmbedding.mixedSpace F),
          G (c : (κ → Af F) ⧸ U) X = Φ (fun i => pairA F ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (X i)) (c i))) ∧
        Φ = ∑ q ∈ T, pureA F (G q) (GlobalTheory.CharForm.cosetInd U q) := by
  first | exact @GlobalTheory.SchACosets.exists_eq_sum_pureA_cosetInd | exact GlobalTheory.SchACosets.exists_eq_sum_pureA_cosetInd | (intros; apply GlobalTheory.SchACosets.exists_eq_sum_pureA_cosetInd <;> assumption)
