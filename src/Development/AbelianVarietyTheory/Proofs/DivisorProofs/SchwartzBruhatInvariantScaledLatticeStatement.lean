import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzBruhatInvariantScaledLattice

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)
open scoped Classical

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.schwartz_bruhat_invariant_scaled_lattice : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ]
    (g : (κ → FiniteAdeleRing (𝓞 F) F) → ℂ), g ∈ SB (κ → FiniteAdeleRing (𝓞 F) F) →
    ∃ d : F, d ≠ 0 ∧ ∀ y, ∀ u ∈ GlobalTheory.EvAdm.scaledInt F κ d, g (y + u) = g y := by
  first | exact @GlobalTheory.EvAdm.exists_scaledInt_invariant_of_SB | exact GlobalTheory.EvAdm.exists_scaledInt_invariant_of_SB | (intros; apply GlobalTheory.EvAdm.exists_scaledInt_invariant_of_SB <;> assumption)
