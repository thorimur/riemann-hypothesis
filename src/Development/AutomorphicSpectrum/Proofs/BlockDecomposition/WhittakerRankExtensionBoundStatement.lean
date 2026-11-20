import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WhittakerRankExtensionBound
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.RgGu
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.whittaker_rank_extension_bound : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ψ : AddChar k Circle), Continuous ψ → ∀ (N : ℕ) {V W₁ W₂ : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W₁] [Module ℂ W₁] [AddCommGroup W₂] [Module ℂ W₂] (ρ : Representation ℂ (GL (Fin N) k) V) (π : Representation ℂ (GL (Fin N) k) W₁) (σ : Representation ℂ (GL (Fin N) k) W₂), IsSmooth ρ → Module.rank ℂ (TwJacquet ρ (unipB k (Fin N)) (whitChar ψ N)) ≤ 1 → π.IsIrreducible → σ.IsIrreducible → IsSubquotient π ρ → IsSubquotient σ ρ → IsGenericFor ψ π → IsGenericFor ψ σ → Nonempty (π.Equiv σ) := by
  first | exact @GlobalTheory.CompanionTheory.GenUniq.nonempty_equiv_of_generic_subquotients | exact GlobalTheory.CompanionTheory.GenUniq.nonempty_equiv_of_generic_subquotients | (intros; apply GlobalTheory.CompanionTheory.GenUniq.nonempty_equiv_of_generic_subquotients <;> assumption)
