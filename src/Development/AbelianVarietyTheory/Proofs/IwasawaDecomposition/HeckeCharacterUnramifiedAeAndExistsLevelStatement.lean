import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeckeCharacterUnramifiedAeAndExistsLevel
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.FrobeniusOrbits Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.L2.Host GlobalTheory.Mem.Chr Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heckeCharacter_unramified_ae_and_exists_level : ∀ (L : Type) [Field L] [NumberField L] (χ : HChar L), {v | ¬ χ.UnrAt v}.Finite ∧ ∀ v, ∃ n, χ.LevelLe v n := by
  first | exact @GlobalTheory.Mem.UnrAe.unr_ae_and_level | exact GlobalTheory.Mem.UnrAe.unr_ae_and_level | (intros; apply GlobalTheory.Mem.UnrAe.unr_ae_and_level <;> assumption)
