import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsIntegralGeneratorSplitPlaceCmExtension
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.KFinLoc
open scoped TensorProduct Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_integral_generator_splitPlace_cmExtension : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    B.IsGood σ → ∀ v : Pl F, Formalism.MainNotions.SchurIrreducible.IsSplit (E := E) v →
    ∃ (a : 𝓞 E) (b c : 𝓞 F), (a : E) ^ 2 + algebraMap F E (b : F) * a + algebraMap F E (c : F) = 0 ∧
      σ (a : E) = -algebraMap F E (b : F) - a ∧ c ∈ v.asIdeal ∧ b ∉ v.asIdeal := by
  first | exact @GlobalTheory.SplitGen.exists_integral_gen_split | exact GlobalTheory.SplitGen.exists_integral_gen_split | (intros; apply GlobalTheory.SplitGen.exists_integral_gen_split <;> assumption)
