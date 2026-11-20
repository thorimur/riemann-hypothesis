import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdealMapSmulIsLatticeOfNeBot
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.KSplit
open scoped Matrix TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ideal_map_smul_isLattice_of_ne_bot : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (n : ℕ) (L : Submodule (𝓞 E) (Fin n → E)) (I : Ideal (𝓞 F)), I ≠ ⊥ → Submodule.IsLattice E L → Submodule.IsLattice E (I.map (algebraMap (𝓞 F) (𝓞 E)) • L) := by
  first | exact @GlobalTheory.ideal_map_smul_isLattice | exact GlobalTheory.ideal_map_smul_isLattice | (intros; apply GlobalTheory.ideal_map_smul_isLattice <;> assumption)
