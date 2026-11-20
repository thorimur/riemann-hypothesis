import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SiegelLineDerivativeCommutator
open scoped TensorProduct NNReal Matrix ComplexConjugate
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.DescB GlobalTheory.ThK.FlagCT GlobalTheory.ThK.FlagPar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.siegel_line_derivative_commutator : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ →
    ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J →
    ∀ γ δ : ℝ → GAd σ J, GlobalTheory.SiegelSet.IsRealLine σ J γ → GlobalTheory.SiegelSet.IsRealLine σ J δ →
      ∃ ε : ℝ → GAd σ J, GlobalTheory.SiegelSet.IsRealLine σ J ε ∧ ∀ f, GlobalTheory.UAut.IsSm σ J f →
        GlobalTheory.SiegelSet.lineDer γ (GlobalTheory.SiegelSet.lineDer δ f) =
          GlobalTheory.SiegelSet.lineDer δ (GlobalTheory.SiegelSet.lineDer γ f) + GlobalTheory.SiegelSet.lineDer ε f := by
  first | exact @GlobalTheory.LeviHC.LineBracket.exists_line_bracket | exact GlobalTheory.LeviHC.LineBracket.exists_line_bracket | (intros; apply GlobalTheory.LeviHC.LineBracket.exists_line_bracket <;> assumption)
