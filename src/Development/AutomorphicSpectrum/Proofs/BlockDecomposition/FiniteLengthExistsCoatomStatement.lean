import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiniteLengthExistsCoatom
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_length_exists_coatom : ∀ {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V), HasFiniteLength ρ → Nontrivial V → ∃ S : Subrepresentation ρ, IsCoatom S := by
  first | exact @GlobalTheory.CompanionTheory.FiniteLengthQuot.exists_isCoatom_subrepresentation | exact GlobalTheory.CompanionTheory.FiniteLengthQuot.exists_isCoatom_subrepresentation | (intros; apply GlobalTheory.CompanionTheory.FiniteLengthQuot.exists_isCoatom_subrepresentation <;> assumption)
