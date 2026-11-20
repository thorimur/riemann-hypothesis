import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSignatureBasisMaxCompact
open scoped TensorProduct NNReal Matrix ComplexConjugate
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.DescB GlobalTheory.ThK.FlagCT GlobalTheory.ThK.FlagPar
open GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.LeviHC
open GlobalTheory.Orb (archMat)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_signature_basis_max_compact : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ →
    ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J →
    ∀ K : Subgroup (GAd σ J), GlobalTheory.UAut.IsMaxCpt σ J K → ∀ (w : InfinitePlace F) (τ : EmbOver E w),
      ∃ (R : Matrix (Fin n) (Fin n) ℂ) (ε : Fin n → Bool),
        Rᴴ * J.map τ.1 * R = Matrix.diagonal (fun i => if ε i then (1 : ℂ) else -1) ∧
        ∀ (Z : Matrix (Fin n) (Fin n) ℂ) (ζ : ℝ → GAd σ J), GlobalTheory.LeviHC.IsLineOf σ J τ Z ζ →
          (R⁻¹ * Z * R)ᴴ = -(R⁻¹ * Z * R) → ∀ s, ζ s ∈ K := by
  first | exact @GlobalTheory.MaxCptFrame.exists_frame_lines_mem | exact GlobalTheory.MaxCptFrame.exists_frame_lines_mem | (intros; apply GlobalTheory.MaxCptFrame.exists_frame_lines_mem <;> assumption)
