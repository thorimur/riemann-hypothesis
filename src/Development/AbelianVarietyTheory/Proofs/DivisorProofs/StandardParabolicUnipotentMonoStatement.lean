import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardParabolicUnipotentMono
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.ThK.SquareIntegrability
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.standardParabolicUnipotent_mono : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ →
    ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ (r : ℕ) (X Y : Matrix (Fin n) (Fin r) E), IsWittFrame σ J X Y →
      ∀ (S T : Finset (Fin r)), T ⊆ S → GlobalTheory.StdPar.unip σ J X T ≤ GlobalTheory.StdPar.unip σ J X S := by
  first | exact @GlobalTheory.StdPar.unip_mono_of_subset | exact GlobalTheory.StdPar.unip_mono_of_subset | (intros; apply GlobalTheory.StdPar.unip_mono_of_subset <;> assumption)
