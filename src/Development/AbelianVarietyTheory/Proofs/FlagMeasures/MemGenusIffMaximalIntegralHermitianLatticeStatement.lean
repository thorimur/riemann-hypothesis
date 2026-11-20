import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MemGenusIffMaximalIntegralHermitianLattice
open NumberField Matrix GlobalTheory.Mass Formalism.HermitianLatticesTheory
open scoped ENNReal Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_genus_iff_maximalIntegralHermitianLattice : ∀ (K V : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (h : V →ₗ⋆[K] V →ₗ[K] K), IsCMUnram K → h.IsSymm → PD h → ∀ M N : Submodule (𝓞 K) V, IsMaxLat h M → (N ∈ genus h M ↔ IsMaxLat h N) := by
  first | exact @GlobalTheory.Mass.MaxGenus.main | exact GlobalTheory.Mass.MaxGenus.main | (intros; apply GlobalTheory.Mass.MaxGenus.main <;> assumption)
