import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WhittakerTwoBlockSubquotientTensor
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.CompanionTheory.BZNuPair
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.whittaker_two_block_subquotient_tensor : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ψ : AddChar k Circle), Continuous ψ → ∀ (d : Fin 2 → ℕ) (X : Type) [AddCommGroup X] [Module ℂ X]
    (J : Representation ℂ (Levi k fun a => Fin (d a)) X), IsSmooth J → HasFiniteLength J → ∀ S : IrrRep (GL (Fin (d 0)) k),
    IsSubquotient S.ρ (whit2 ψ d J) → ∃ s : ∀ a, IrrRep (GL (Fin (d a)) k),
      IsSubquotient (piTensor fun a => (s a).ρ) J ∧ Nonempty ((s 0).ρ.Equiv S.ρ) := by
  first | exact @GlobalTheory.CompanionTheory.BZNuPair.exists_constituent_of_whit2 | exact GlobalTheory.CompanionTheory.BZNuPair.exists_constituent_of_whit2 | (intros; apply GlobalTheory.CompanionTheory.BZNuPair.exists_constituent_of_whit2 <;> assumption)
