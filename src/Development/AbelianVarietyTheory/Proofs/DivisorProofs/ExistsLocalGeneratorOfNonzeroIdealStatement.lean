import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLocalGeneratorOfNonzeroIdeal
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.KSplit
open scoped Matrix TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_local_generator_of_nonzero_ideal : ∀ (F : Type) [Field F] [NumberField F] (I : Ideal (𝓞 F)) (v : IsDedekindDomain.HeightOneSpectrum (𝓞 F)), I ≠ ⊥ → ∃ z : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v, z ≠ 0 ∧ (¬ I ≤ v.asIdeal → z = 1) ∧ (∀ d ∈ I, Valued.v (algebraMap F (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) (d : F)) ≤ Valued.v z) ∧ ∃ d ∈ I, Valued.v (algebraMap F (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) (d : F)) = Valued.v z := by
  first | exact @GlobalTheory.ideal_localGenerator | exact GlobalTheory.ideal_localGenerator | (intros; apply GlobalTheory.ideal_localGenerator <;> assumption)
