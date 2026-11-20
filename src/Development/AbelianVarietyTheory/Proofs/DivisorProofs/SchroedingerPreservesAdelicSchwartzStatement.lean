import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchroedingerPreservesAdelicSchwartz
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.WeilTr MeasureTheory
open scoped Matrix ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.schroedinger_preserves_adelic_schwartz : ∀ (F : Type) [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ), IsStd ψ → ∀ (κ : Type) [Fintype κ]
    (p : (κ → AF F) × (κ → AF F)), ∀ Φ ∈ schA F κ, schr ψ p Φ ∈ schA F κ := by
  first | exact @GlobalTheory.SchrKeepsSchA.schr_mem_schA | exact GlobalTheory.SchrKeepsSchA.schr_mem_schA | (intros; apply GlobalTheory.SchrKeepsSchA.schr_mem_schA <;> assumption)
