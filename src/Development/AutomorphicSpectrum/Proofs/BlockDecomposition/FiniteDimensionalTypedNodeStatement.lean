import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiniteDimensionalTypedNode
open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec GlobalTheory.CompanionTheory.CTFin PositivityTheory.Rg.Rs PositivityTheory.Rg.Rs.InducedTensorMap
open PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.SpectralAccumulation GlobalTheory.CompanionTheory.LimV
open scoped ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finiteDimensional_typed_node : ∀ {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {r s : ℕ} (U₁ : Submodule ℂ (Sm E r)) (U₂ : Submodule ℂ (Sm E s)), (∀ (K : Subgroup (GL (Fin r) (Af E))) (W : Submodule ℂ (Kinf E r → ℂ)), IsOpen (K : Set (GL (Fin r) (Af E))) → FiniteDimensional ℂ W → FiniteDimensional ℂ (typed U₁ K W)) → (∀ (K : Subgroup (GL (Fin s) (Af E))) (W : Submodule ℂ (Kinf E s → ℂ)), IsOpen (K : Set (GL (Fin s) (Af E))) → FiniteDimensional ℂ W → FiniteDimensional ℂ (typed U₂ K W)) → ∀ (K : Subgroup (GL (Fin (r + s)) (Af E))) (W : Submodule ℂ (Kinf E (r + s) → ℂ)), IsOpen (K : Set (GL (Fin (r + s)) (Af E))) → FiniteDimensional ℂ W → FiniteDimensional ℂ (typed (indSpan U₁ U₂) K W) := by
  first | exact @GlobalTheory.CompanionTheory.LimV.FdNode.finiteDimensional_typed_indSpan | exact GlobalTheory.CompanionTheory.LimV.FdNode.finiteDimensional_typed_indSpan | (intros; apply GlobalTheory.CompanionTheory.LimV.FdNode.finiteDimensional_typed_indSpan <;> assumption)
