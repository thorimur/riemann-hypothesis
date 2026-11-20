import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsUnitarizableComplexRepOfSupercuspidalUnitaryCentralCharacter
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isUnitarisableComplexRep_of_supercuspidal_unitary_center : ∀ (G V : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V) (l : Module.Dual ℂ V), l ∈ smoothPart ρ.dual → l ≠ 0 → ρ.IsIrreducible → IsSupercuspidal ρ → (∀ z ∈ Subgroup.center G, ∃ c : ℂ, ‖c‖ = 1 ∧ ∀ v, ρ z v = c • v) → IsUnitarisable ρ := by
  first | exact @GlobalTheory.isUnitarisable_of_isSupercuspidal | exact GlobalTheory.isUnitarisable_of_isSupercuspidal | (intros; apply GlobalTheory.isUnitarisable_of_isSupercuspidal <;> assumption)
